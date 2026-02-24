use alloc::vec::Vec;

use digest::Digest;
use generic_ec::{Curve, NonZero, Point, Scalar, SecretScalar};
use generic_ec_zkp::{polynomial::Polynomial, schnorr_pok};
use rand_core::{CryptoRng, RngCore};
use round_based::{
    rounds_router::simple_store::RoundInput, rounds_router::RoundsRouter, Delivery, Mpc, MpcParty,
    Outgoing, ProtocolMessage, SinkExt,
};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::progress::Tracer;
use crate::{
    errors::IoError,
    key_share::{CoreKeyShare, DirtyCoreKeyShare, DirtyKeyInfo, Validate, VssSetup},
    security_level::SecurityLevel,
    utils, ExecutionId,
};

use super::{Bug, KeygenAborted, KeygenError};

macro_rules! prefixed {
    ($name:tt) => {
        concat!("dfns.cggmp24.keygen.threshold.", $name)
    };
}

/// Message of key generation protocol
#[derive(ProtocolMessage, Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub enum Msg<E: Curve, L: SecurityLevel, D: Digest> {
    /// Round 1 message
    Round1(MsgRound1<D>),
    /// Round 2a message
    Round2Broad(MsgRound2Broad<E, L>),
    /// Round 2b message
    Round2Uni(MsgRound2Uni<E>),
    /// Round 3 message
    Round3(MsgRound3<E>),
    /// Reliability check message (optional additional round)
    ReliabilityCheck(MsgReliabilityCheck<D>),
}

/// Message from round 1
#[derive(Clone, Serialize, Deserialize, udigest::Digestable)]
#[serde(bound = "")]
#[udigest(bound = "")]
#[udigest(tag = prefixed!("round1"))]
pub struct MsgRound1<D: Digest> {
    /// $V_i$
    #[udigest(as_bytes)]
    pub commitment: digest::Output<D>,
}
/// Message from round 2 broadcasted to everyone
#[serde_as]
#[derive(Clone, Serialize, Deserialize, udigest::Digestable)]
#[serde(bound = "")]
#[udigest(bound = "")]
#[udigest(tag = prefixed!("round2_broad"))]
pub struct MsgRound2Broad<E: Curve, L: SecurityLevel> {
    /// `rid_i`
    #[serde_as(as = "utils::HexOrBin")]
    #[udigest(as_bytes)]
    pub rid: L::KappaBytes,
    /// $\vec S_i$
    pub F: Polynomial<Point<E>>,
    /// $A_i$
    pub sch_commit: schnorr_pok::Commit<E>,
    /// Party contribution to chain code
    #[cfg(feature = "hd-wallet")]
    #[serde_as(as = "Option<utils::HexOrBin>")]
    #[udigest(as = Option<udigest::Bytes>)]
    pub chain_code: Option<hd_wallet::ChainCode>,
    /// $u_i$
    #[serde(with = "hex::serde")]
    #[udigest(as_bytes)]
    pub decommit: L::KappaBytes,
}
/// Message from round 2 unicasted to each party
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct MsgRound2Uni<E: Curve> {
    /// $\sigma_{i,j}$
    pub sigma: Scalar<E>,
}
/// Message from round 3
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct MsgRound3<E: Curve> {
    /// $\psi_i$
    pub sch_proof: schnorr_pok::Proof<E>,
}
/// Message parties exchange to ensure reliability of broadcast channel
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct MsgReliabilityCheck<D: Digest>(pub digest::Output<D>);

mod unambiguous {
    use generic_ec::{Curve, NonZero, Point};

    use crate::{ExecutionId, SecurityLevel};

    #[derive(udigest::Digestable)]
    #[udigest(tag = prefixed!("hash_commitment"))]
    #[udigest(bound = "")]
    pub struct HashCom<'a, E: Curve, L: SecurityLevel> {
        pub sid: ExecutionId<'a>,
        pub party_index: u16,
        pub decommitment: &'a super::MsgRound2Broad<E, L>,
    }

    #[derive(udigest::Digestable)]
    #[udigest(tag = prefixed!("schnorr_pok"))]
    #[udigest(bound = "")]
    pub struct SchnorrPok<'a, E: Curve> {
        pub sid: ExecutionId<'a>,
        pub prover: u16,
        #[udigest(as_bytes)]
        pub rid: &'a [u8],
        pub y: NonZero<Point<E>>,
        pub h: Point<E>,
    }

    #[derive(udigest::Digestable)]
    #[udigest(tag = prefixed!("echo_round"))]
    #[udigest(bound = "")]
    pub struct Echo<'a, D: digest::Digest> {
        pub sid: ExecutionId<'a>,
        pub commitment: &'a super::MsgRound1<D>,
    }
}


// 核心部分
pub async fn run_threshold_keygen<E, R, M, L, D>(
    mut tracer: Option<&mut dyn Tracer>,
    i: u16,  // 我是谁（第 i 号参与者）
    t: u16,  // 阈值（最少要 t 个人才能签名）
    n: u16,  // 一共有多少人
    reliable_broadcast_enforced: bool,  // 是否做额外的“大家看到的广播内容一致吗？”检查
    sid: ExecutionId<'_>,  // 这次协议的“会话编号”（防止别人把旧消息拿来骗你）
    rng: &mut R,  // 随机数生成器（所有安全都靠随机数）
    party: M,  // 
    #[cfg(feature = "hd-wallet")] hd_enabled: bool,
) -> Result<CoreKeyShare<E>, KeygenError>
where
    E: Curve,
    L: SecurityLevel,
    D: Digest + Clone + 'static,
    R: RngCore + CryptoRng,
    M: Mpc<ProtocolMessage = Msg<E, L, D>>,
{
    tracer.protocol_begins();

    tracer.stage("Setup networking");
    let MpcParty { delivery, .. } = party.into_party();
    let (incomings, mut outgoings) = delivery.split();

    let mut rounds = RoundsRouter::<Msg<E, L, D>>::builder();
    let round1 = rounds.add_round(RoundInput::<MsgRound1<D>>::broadcast(i, n));
    let round1_sync = rounds.add_round(RoundInput::<MsgReliabilityCheck<D>>::broadcast(i, n));
    let round2_broad = rounds.add_round(RoundInput::<MsgRound2Broad<E, L>>::broadcast(i, n));
    let round2_uni = rounds.add_round(RoundInput::<MsgRound2Uni<E>>::p2p(i, n));
    let round3 = rounds.add_round(RoundInput::<MsgRound3<E>>::broadcast(i, n));
    let mut rounds = rounds.listen(incomings);

    // Round 1 ： 每个人生成自己的“阈值秘密结构”，然后只发一个哈希commitment
    tracer.round_begins();

    tracer.stage("Sample rid_i, schnorr commitment, polynomial, chain_code");
    let mut rid = L::KappaBytes::default();
    // 生成我的 rid_i：随机字节串
    rng.fill_bytes(rid.as_mut());

    // 为 Schnorr 证明准备 commit
    // h 就是我之后要公开的 “A_i”
    // r 是我私下留着的临时随机数，后面生成证明用
    let (r, h) = schnorr_pok::prover_commits_ephemeral_secret::<E, _>(rng);

    // 生成 Shamir 多项式（阈值核心）
    // 我随机生成一个次数为 t-1 的多项式 f(x)
    let f = Polynomial::<SecretScalar<E>>::sample(rng, usize::from(t) - 1);
    // 生成公开commitment F（Feldman VSS）
    // 把多项式的系数都“乘上生成元 G”变成曲线点
    let F = &f * &Point::generator();
    // 预计算我要发给每个人的私下份额 sigma_{i->j}
    // 对每个参与者 j，我算一个数 sigma = f(j+1)
    let sigmas = (0..n)
        .map(|j| {
            let x = Scalar::from(j + 1);
            f.value(&x)
        })
        .collect::<Vec<_>>();
    debug_assert_eq!(sigmas.len(), usize::from(n));

    #[cfg(feature = "hd-wallet")]
    let chain_code_local = if hd_enabled {
        let mut chain_code = hd_wallet::ChainCode::default();
        rng.fill_bytes(&mut chain_code);
        Some(chain_code)
    } else {
        None
    };

    tracer.stage("Commit to public data");
    // 生成我 Round2 要公开的内容（decommitment）
    let my_decommitment = MsgRound2Broad {
        rid,
        F: F.clone(),
        sch_commit: h,
        #[cfg(feature = "hd-wallet")]
        chain_code: chain_code_local,
        decommit: {
            let mut nonce = L::KappaBytes::default();
            rng.fill_bytes(nonce.as_mut());
            nonce
        },
    };
    let hash_commit = udigest::hash::<D>(&unambiguous::HashCom {
        sid,
        party_index: i,
        decommitment: &my_decommitment,
    });

    tracer.send_msg();
    let my_commitment = MsgRound1 {
        commitment: hash_commit,
    };
    // 封装：outgoings 发送广播消息：我的 commitment
    outgoings
        .send(Outgoing::broadcast(Msg::Round1(my_commitment.clone())))
        .await
        .map_err(IoError::send_message)?;
    tracer.msg_sent();

    // Round 2：收齐大家的承诺，然后公开我的内容 + 私下发份额
    tracer.round_begins();

    tracer.receive_msgs();
    // 收到所有人的 Round1 承诺
    let commitments = rounds
        .complete(round1)
        .await
        .map_err(IoError::receive_message)?;
    tracer.msgs_received();

    // Optional reliability check
    // 如果开启：
        // 我把我看到的 commitments 全部 hash 得到 h_i
        // 广播 h_i
        // 看别人发的 h_j 是否等于 h_i
        // 不等就 abort
    if reliable_broadcast_enforced {
        tracer.stage("Hash received msgs (reliability check)");
        let h_i = udigest::hash_iter::<D>(
            commitments
                .iter_including_me(&my_commitment)
                .map(|commitment| unambiguous::Echo { sid, commitment }),
        );

        tracer.send_msg();
        outgoings
            .send(Outgoing::broadcast(Msg::ReliabilityCheck(
                MsgReliabilityCheck(h_i.clone()),
            )))
            .await
            .map_err(IoError::send_message)?;
        tracer.msg_sent();

        tracer.round_begins();

        tracer.receive_msgs();
        let hashes = rounds
            .complete(round1_sync)
            .await
            .map_err(IoError::receive_message)?;
        tracer.msgs_received();

        tracer.stage("Assert other parties hashed messages (reliability check)");
        let parties_have_different_hashes = hashes
            .into_iter_indexed()
            .filter(|(_j, _msg_id, h_j)| h_i != h_j.0)
            .map(|(j, msg_id, _)| (j, msg_id))
            .collect::<Vec<_>>();
        if !parties_have_different_hashes.is_empty() {
            return Err(KeygenAborted::Round1NotReliable(parties_have_different_hashes).into());
        }
    }

    tracer.send_msg();
    // 广播我的 decommitment（Round2Broad）
    outgoings
        .feed(Outgoing::broadcast(Msg::Round2Broad(
            my_decommitment.clone(),
        )))
        .await
        .map_err(IoError::send_message)?;

    // 给每个其他人私下发 sigma （Round2Uni）
    let messages = utils::iter_peers(i, n).map(|j| {
        let message = MsgRound2Uni {
            sigma: sigmas[usize::from(j)],
        };
        Outgoing::p2p(j, Msg::Round2Uni(message))
    });
    outgoings
        .send_all(&mut futures_util::stream::iter(messages.map(Ok)))
        .await
        .map_err(IoError::send_message)?;
    tracer.msg_sent();

    // Round 3 ： 最关键的安全检查 + 生成最终份额 + Schnorr 证明
    tracer.round_begins();

    tracer.receive_msgs();
    // 收到所有人的 Round2Broad 和 Round2Uni
    let decommitments = rounds
        .complete(round2_broad)
        .await
        .map_err(IoError::receive_message)?;
    let sigmas_msg = rounds
        .complete(round2_uni)
        .await
        .map_err(IoError::receive_message)?;
    tracer.msgs_received();

    tracer.stage("Validate decommitments");
    // 检查：Round2Broad 是否匹配 Round1 的 commitment
    let blame = utils::collect_blame(&commitments, &decommitments, |j, com, decom| {
        let com_expected = udigest::hash::<D>(&unambiguous::HashCom {
            sid,
            party_index: j,
            decommitment: decom,
        });
        com.commitment != com_expected
    });
    if !blame.is_empty() {
        return Err(KeygenAborted::InvalidDecommitment(blame).into());
    }

    tracer.stage("Validate data size");
    // 检查：多项式次数是否正确（必须 t-1）
    let blame = decommitments
        .iter_indexed()
        .filter(|(_, _, d)| d.F.degree() + 1 != usize::from(t))
        .map(|t| t.0)
        .collect::<Vec<_>>();
    if !blame.is_empty() {
        return Err(KeygenAborted::InvalidDataSize { parties: blame }.into());
    }

    tracer.stage("Validate Feldmann VSS");
    // Feldman VSS 检查：他私下给你的 sigma 是否和他公开的 F 匹配
    let blame = decommitments
        .iter_indexed()
        .zip(sigmas_msg.iter())
        .filter(|((_, _, d), s)| {
            d.F.value::<_, Point<_>>(&Scalar::from(i + 1)) != Point::generator() * s.sigma
        })
        .map(|t| t.0 .0)
        .collect::<Vec<_>>();
    if !blame.is_empty() {
        return Err(KeygenAborted::FeldmanVerificationFailed { parties: blame }.into());
    }

    tracer.stage("Compute rid");
    // 计算全局 rid（大家的 rid XOR）
    let rid = decommitments
        .iter_including_me(&my_decommitment)
        .map(|d| &d.rid)
        .fold(L::KappaBytes::default(), utils::xor_array);
    #[cfg(feature = "hd-wallet")]
    let chain_code = if hd_enabled {
        tracer.stage("Compute chain_code");
        let blame = utils::collect_simple_blame(&decommitments, |decom| decom.chain_code.is_none());
        if !blame.is_empty() {
            return Err(KeygenAborted::MissingChainCode(blame).into());
        }
        Some(decommitments.iter_including_me(&my_decommitment).try_fold(
            hd_wallet::ChainCode::default(),
            |acc, decom| {
                Ok::<_, Bug>(utils::xor_array(
                    acc,
                    decom.chain_code.ok_or(Bug::NoChainCode)?,
                ))
            },
        )?)
    } else {
        None
    };
    tracer.stage("Compute Ys");
    // 计算所有人的公开份额 Ys（每个人最终的公钥 share）
    let polynomial_sum = decommitments
        .iter_including_me(&my_decommitment)
        .map(|d| &d.F)
        .sum::<Polynomial<_>>();
    let ys = (0..n)
        .map(|l| polynomial_sum.value(&Scalar::from(l + 1)))
        .map(|y_j: Point<E>| NonZero::from_point(y_j).ok_or(Bug::ZeroShare))
        .collect::<Result<Vec<_>, _>>()?;
    tracer.stage("Compute sigma");
    // 计算我自己的最终秘密份额 sigma_i
    let sigma: Scalar<E> = sigmas_msg.iter().map(|msg| msg.sigma).sum();
    let mut sigma = sigma + sigmas[usize::from(i)];
    let sigma = NonZero::from_secret_scalar(SecretScalar::new(&mut sigma)).ok_or(Bug::ZeroShare)?;
    debug_assert_eq!(Point::generator() * &sigma, ys[usize::from(i)]);

    tracer.stage("Calculate challenge");
    // 生成 Schnorr 证明：证明我知道 sigma_i
    let challenge = Scalar::from_hash::<D>(&unambiguous::SchnorrPok {
        sid,
        prover: i,
        rid: rid.as_ref(),
        y: ys[usize::from(i)],
        h: my_decommitment.sch_commit.0,
    });
    let challenge = schnorr_pok::Challenge { nonce: challenge };

    tracer.stage("Prove knowledge of `sigma_i`");
    let z = schnorr_pok::prove(&r, &challenge, &sigma);

    tracer.send_msg();
    let my_sch_proof = MsgRound3 { sch_proof: z };
    outgoings
        .send(Outgoing::broadcast(Msg::Round3(my_sch_proof.clone())))
        .await
        .map_err(IoError::send_message)?;
    tracer.msg_sent();

    // Output round ： 验证所有人的 Schnorr 证明，得到最终公钥
    tracer.round_begins();

    tracer.receive_msgs();
    // 收到所有人的 Round3 proof
    let sch_proofs = rounds
        .complete(round3)
        .await
        .map_err(IoError::receive_message)?;
    tracer.msgs_received();

    tracer.stage("Validate schnorr proofs");
    // 验证每个人的 Schnorr proof
    let blame = utils::collect_blame(&decommitments, &sch_proofs, |j, decom, sch_proof| {
        let challenge = Scalar::from_hash::<D>(&unambiguous::SchnorrPok {
            sid,
            prover: j,
            rid: rid.as_ref(),
            y: ys[usize::from(j)],
            h: decom.sch_commit.0,
        });
        let challenge = schnorr_pok::Challenge { nonce: challenge };
        sch_proof
            .sch_proof
            .verify(&decom.sch_commit, &challenge, &ys[usize::from(j)])
            .is_err()
    });
    if !blame.is_empty() {
        return Err(KeygenAborted::InvalidSchnorrProof(blame).into());
    }

    tracer.stage("Derive resulting public key and other data");
    // 得到最终公钥 y（总公钥）
    let y: Point<E> = decommitments
        .iter_including_me(&my_decommitment)
        .map(|d| d.F.coefs()[0])
        .sum();
    let key_shares_indexes = (1..=n)
        .map(|i| NonZero::from_scalar(Scalar::from(i)))
        .collect::<Option<Vec<_>>>()
        .ok_or(Bug::NonZeroScalar)?;

    tracer.protocol_ends();

    // 返回结果：我本地要保存的东西
    // shared_public_key = y
    // public_shares = ys
    // min_signers = t
    // x = sigma (我自己的秘密份额)
    Ok(DirtyCoreKeyShare {
        i,
        key_info: DirtyKeyInfo {
            curve: Default::default(),
            shared_public_key: NonZero::from_point(y).ok_or(Bug::ZeroPk)?,
            public_shares: ys,
            vss_setup: Some(VssSetup {
                min_signers: t,
                I: key_shares_indexes,
            }),
            #[cfg(feature = "hd-wallet")]
            chain_code,
        },
        x: sigma,
    }
    .validate()
    .map_err(|err| Bug::InvalidKeyShare(err.into_error()))?)
}
