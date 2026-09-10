import Synthesis.Core.Identity

namespace Synthesis
set_option autoImplicit false

/-- Algorithm contract identifies both algorithm and byte convention. Digests are
fingerprints, not proofs of semantic equality or authentication. -/
structure ContentDigest where
  scheme : ContractId
  bytes : List UInt8
  deriving Repr, DecidableEq, BEq

/-- Portable FNV-1a-64, big-endian digest bytes. Noncryptographic: useful for accidental
change detection only. Never use this scheme alone as adversarial content identity. -/
def fingerprint (bytes : ByteArray) : ContentDigest :=
  let value := bytes.foldl (fun (h : UInt64) byte => (h ^^^ byte.toUInt64) * 1099511628211)
    14695981039346656037
  ⟨.named "synthesis.fingerprint" "fnv1a64-be" 1,
    [56, 48, 40, 32, 24, 16, 8, 0].map (fun shift => (value >>> UInt64.ofNat shift).toUInt8)⟩

/-- Explicit immutable logical revision, optionally bound to a content fingerprint.
Owners must never reuse (identity, version) for different content. A fingerprint
supplements this contract; it does not establish collision-free identity. -/
structure RevisionRef where
  identity : QualifiedId
  version : Symbol
  content : Option ContentDigest := none
  deriving Repr, DecidableEq, BEq

def ContentDigest.hex (digest : ContentDigest) : String :=
  String.join (digest.bytes.map fun byte => String.ofList
    [Nat.digitChar (byte.toNat / 16), Nat.digitChar (byte.toNat % 16)])

end Synthesis
