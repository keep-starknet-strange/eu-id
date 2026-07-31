//! SHAKE-128 / SHAKE-256 sponge wrappers that *record* their absorb and squeeze
//! byte streams.
//!
//! The reference records each Keccak permutation for witness generation.
//! Each invocation logs its exact input and output bytes.
//! Tests compare the in-circuit sponge with the recorded [`SpongeTranscript`].
//!
//! FIPS 204 uses two XOFs (§3.7, "H denotes SHAKE-256, G denotes SHAKE-128"):
//! - SHAKE-256 for `tr`, `µ`, `c̃`, and `SampleInBall`,
//! - SHAKE-128 for `RejNTTPoly` inside `ExpandA`.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake128, Shake256};

/// A recorded XOF invocation: the concatenated absorbed input and the squeezed
/// output. Two transcripts with the same `absorbed` must produce the same
/// `squeezed` prefix. The in-circuit sponge checks this invariant.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SpongeTranscript {
    /// Every byte absorbed, in order (concatenation of all `absorb` calls).
    pub absorbed: Vec<u8>,
    /// Every byte squeezed out, in order.
    pub squeezed: Vec<u8>,
}

/// SHAKE-256 (`H`) over the concatenation of `inputs`, squeezing `out_len`
/// bytes, recording the transcript.
pub fn shake256(inputs: &[&[u8]], out_len: usize) -> (Vec<u8>, SpongeTranscript) {
    let mut hasher = Shake256::default();
    let mut absorbed = Vec::new();
    for chunk in inputs {
        hasher.update(chunk);
        absorbed.extend_from_slice(chunk);
    }
    let mut reader = hasher.finalize_xof();
    let mut squeezed = vec![0u8; out_len];
    reader.read(&mut squeezed);
    let transcript = SpongeTranscript {
        absorbed,
        squeezed: squeezed.clone(),
    };
    (squeezed, transcript)
}

/// SHAKE-128 (`G`) over the concatenation of `inputs`, squeezing `out_len`
/// bytes, recording the transcript. Used where `RejNTTPoly` needs a bounded
/// prefix; for the streaming rejection sampler use [`Shake128Reader`].
pub fn shake128(inputs: &[&[u8]], out_len: usize) -> (Vec<u8>, SpongeTranscript) {
    let mut hasher = Shake128::default();
    let mut absorbed = Vec::new();
    for chunk in inputs {
        hasher.update(chunk);
        absorbed.extend_from_slice(chunk);
    }
    let mut reader = hasher.finalize_xof();
    let mut squeezed = vec![0u8; out_len];
    reader.read(&mut squeezed);
    let transcript = SpongeTranscript {
        absorbed,
        squeezed: squeezed.clone(),
    };
    (squeezed, transcript)
}

/// A streaming SHAKE-256 reader for `SampleInBall`, which squeezes one rate
/// block at a time until τ coefficients are placed (FIPS 204 Algorithm 29).
/// Records everything it absorbs and squeezes.
pub struct Shake256Reader {
    reader: sha3::Shake256Reader,
    transcript: SpongeTranscript,
}

impl Shake256Reader {
    /// Absorb `inputs`, finalize, and prepare to stream output.
    pub fn new(inputs: &[&[u8]]) -> Self {
        let mut hasher = Shake256::default();
        let mut absorbed = Vec::new();
        for chunk in inputs {
            hasher.update(chunk);
            absorbed.extend_from_slice(chunk);
        }
        Self {
            reader: hasher.finalize_xof(),
            transcript: SpongeTranscript {
                absorbed,
                squeezed: Vec::new(),
            },
        }
    }

    /// Squeeze the next `n` bytes, appending them to the recorded transcript.
    pub fn read(&mut self, n: usize) -> Vec<u8> {
        let mut out = vec![0u8; n];
        self.reader.read(&mut out);
        self.transcript.squeezed.extend_from_slice(&out);
        out
    }

    /// The transcript recorded so far.
    pub fn transcript(&self) -> &SpongeTranscript {
        &self.transcript
    }
}

/// A streaming SHAKE-128 reader for `RejNTTPoly`, which squeezes an
/// unbounded stream 3 bytes at a time until 256 coefficients are accepted
/// (FIPS 204 Algorithm 30). Records everything it absorbs and squeezes.
pub struct Shake128Reader {
    reader: sha3::Shake128Reader,
    transcript: SpongeTranscript,
}

impl Shake128Reader {
    /// Absorb `inputs`, finalize, and prepare to stream output.
    pub fn new(inputs: &[&[u8]]) -> Self {
        let mut hasher = Shake128::default();
        let mut absorbed = Vec::new();
        for chunk in inputs {
            hasher.update(chunk);
            absorbed.extend_from_slice(chunk);
        }
        Self {
            reader: hasher.finalize_xof(),
            transcript: SpongeTranscript {
                absorbed,
                squeezed: Vec::new(),
            },
        }
    }

    /// Squeeze the next `n` bytes, appending them to the recorded transcript.
    pub fn read(&mut self, n: usize) -> Vec<u8> {
        let mut out = vec![0u8; n];
        self.reader.read(&mut out);
        self.transcript.squeezed.extend_from_slice(&out);
        out
    }

    /// The transcript recorded so far.
    pub fn transcript(&self) -> &SpongeTranscript {
        &self.transcript
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shake256_records_and_is_deterministic() {
        let (out_a, t_a) = shake256(&[b"ab", b"c"], 32);
        let (out_b, t_b) = shake256(&[b"abc"], 32);
        assert_eq!(out_a, out_b, "absorb chunking must not change the output");
        assert_eq!(t_a.absorbed, b"abc");
        assert_eq!(t_a.squeezed, out_a);
        assert_eq!(t_b.absorbed, b"abc");
    }

    #[test]
    fn shake128_streaming_matches_bulk() {
        let (bulk, _) = shake128(&[b"seed"], 12);
        let mut r = Shake128Reader::new(&[b"seed"]);
        let mut streamed = r.read(3);
        streamed.extend(r.read(9));
        assert_eq!(bulk, streamed);
        assert_eq!(r.transcript().absorbed, b"seed");
        assert_eq!(r.transcript().squeezed, streamed);
    }
}
