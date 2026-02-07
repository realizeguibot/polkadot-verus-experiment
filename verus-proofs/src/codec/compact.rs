use vstd::prelude::*;

verus! {

// ============================================================================
// SCALE Compact<u32> encoding specification
//
// Reference: https://docs.substrate.io/reference/scale-codec/
//
// Mode       | Range              | Encoding
// -----------|--------------------|-----------------------------------------
// single-byte| 0..=63             | (val*4 + 0) as 1 byte
// two-byte   | 64..=16383         | (val*4 + 1) as 2 bytes LE
// four-byte  | 16384..=1073741823 | (val*4 + 2) as 4 bytes LE
// big-integer| larger             | prefix byte 0x03, then 4 LE bytes of val
//
// The low 2 bits of the first byte encode the mode (0,1,2,3).
// The value is stored in the remaining bits (shifted left by 2).
//
// We use integer arithmetic (*, /, %) instead of bit shifts to avoid
// type issues in Verus spec mode where bitwise ops on u32 return int.
// ============================================================================

/// Extract byte k (0-indexed from LSB) from an integer
pub open spec fn byte_at(x: int, k: nat) -> u8
    recommends 0 <= x,
{
    ((x / pow2(k * 8)) % 256) as u8
}

/// Reconstruct an integer from 2 LE bytes
pub open spec fn from_le_2(b0: u8, b1: u8) -> int {
    b0 as int + (b1 as int) * 256
}

/// Reconstruct an integer from 4 LE bytes
pub open spec fn from_le_4(b0: u8, b1: u8, b2: u8, b3: u8) -> int {
    b0 as int + (b1 as int) * 256 + (b2 as int) * 65536 + (b3 as int) * 16777216
}

/// Powers of 2 (for byte extraction)
pub open spec fn pow2(n: nat) -> int
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

/// Number of bytes used by compact encoding of a u32 value
pub open spec fn compact_encoded_len(val: u32) -> nat {
    if val <= 63 {
        1
    } else if val <= 16383 {
        2
    } else if val <= 1073741823 {
        4
    } else {
        5
    }
}

/// Encode a u32 in SCALE compact format, returning a Seq<u8>
pub open spec fn compact_encode(val: u32) -> Seq<u8> {
    let v = val as int;
    if val <= 63 {
        // Single byte: val*4, mode bits = 00
        seq![(v * 4) as u8]
    } else if val <= 16383 {
        // Two bytes LE: val*4 + 1, mode bits = 01
        let encoded = v * 4 + 1;
        seq![
            byte_at(encoded, 0),
            byte_at(encoded, 1)
        ]
    } else if val <= 1073741823 {
        // Four bytes LE: val*4 + 2, mode bits = 10
        let encoded = v * 4 + 2;
        seq![
            byte_at(encoded, 0),
            byte_at(encoded, 1),
            byte_at(encoded, 2),
            byte_at(encoded, 3)
        ]
    } else {
        // Big-integer mode: prefix 0x03, then 4 LE bytes of val
        seq![
            0x03u8,
            byte_at(v, 0),
            byte_at(v, 1),
            byte_at(v, 2),
            byte_at(v, 3)
        ]
    }
}

/// Decode a compact u32 from the start of a byte sequence.
/// Returns Some((value, bytes_consumed)) or None on failure.
pub open spec fn compact_decode(bytes: Seq<u8>) -> Option<(u32, nat)> {
    if bytes.len() == 0 {
        None
    } else {
        let mode = (bytes[0] as int) % 4;
        if mode == 0 {
            // Single-byte: value = first_byte / 4
            Some(((bytes[0] as int / 4) as u32, 1))
        } else if mode == 1 {
            // Two-byte LE
            if bytes.len() < 2 {
                None
            } else {
                let raw = from_le_2(bytes[0], bytes[1]);
                Some(((raw / 4) as u32, 2))
            }
        } else if mode == 2 {
            // Four-byte LE
            if bytes.len() < 4 {
                None
            } else {
                let raw = from_le_4(bytes[0], bytes[1], bytes[2], bytes[3]);
                Some(((raw / 4) as u32, 4))
            }
        } else {
            // mode == 3: big-integer mode
            // For u32: prefix byte is 0x03 (byte_count = 4)
            if bytes.len() < 5 {
                None
            } else {
                let byte_count = (bytes[0] as int) / 4 + 4;
                if byte_count != 4 {
                    None
                } else {
                    let val = from_le_4(bytes[1], bytes[2], bytes[3], bytes[4]);
                    Some((val as u32, 5))
                }
            }
        }
    }
}

// --- Helper lemmas for pow2 ---

proof fn lemma_pow2_values()
    ensures
        pow2(0) == 1,
        pow2(8) == 256,
        pow2(16) == 65536,
        pow2(24) == 16777216,
        pow2(32) == 4294967296int,
{
    reveal(pow2);
    assert(pow2(0) == 1);
    assert(pow2(1) == 2);
    assert(pow2(2) == 4);
    assert(pow2(3) == 8);
    assert(pow2(4) == 16);
    assert(pow2(5) == 32);
    assert(pow2(6) == 64);
    assert(pow2(7) == 128);
    assert(pow2(8) == 256);
    assert(pow2(9) == 512);
    assert(pow2(10) == 1024);
    assert(pow2(11) == 2048);
    assert(pow2(12) == 4096);
    assert(pow2(13) == 8192);
    assert(pow2(14) == 16384);
    assert(pow2(15) == 32768);
    assert(pow2(16) == 65536);
    assert(pow2(17) == 131072);
    assert(pow2(18) == 262144);
    assert(pow2(19) == 524288);
    assert(pow2(20) == 1048576);
    assert(pow2(21) == 2097152);
    assert(pow2(22) == 4194304);
    assert(pow2(23) == 8388608);
    assert(pow2(24) == 16777216);
    assert(pow2(25) == 33554432);
    assert(pow2(26) == 67108864);
    assert(pow2(27) == 134217728);
    assert(pow2(28) == 268435456);
    assert(pow2(29) == 536870912);
    assert(pow2(30) == 1073741824);
    assert(pow2(31) == 2147483648int);
    assert(pow2(32) == 4294967296int);
}

/// Helper: byte_at extracts the correct byte for small values
proof fn lemma_byte_at_basics(x: int)
    requires 0 <= x,
    ensures
        byte_at(x, 0) == (x % 256) as u8,
        byte_at(x, 1) == ((x / 256) % 256) as u8,
        byte_at(x, 2) == ((x / 65536) % 256) as u8,
        byte_at(x, 3) == ((x / 16777216) % 256) as u8,
{
    lemma_pow2_values();
    reveal(pow2);
}

/// Helper: LE byte reassembly roundtrips for values < 2^16
proof fn lemma_le2_roundtrip(x: int)
    requires 0 <= x < 65536,
    ensures from_le_2(byte_at(x, 0), byte_at(x, 1)) == x,
{
    lemma_byte_at_basics(x);
    // from_le_2(byte_at(x, 0), byte_at(x, 1))
    //   = (x % 256) + ((x / 256) % 256) * 256
    //   = (x % 256) + (x / 256) * 256    (because x / 256 < 256 when x < 65536)
    //   = x
    assert((x / 256) < 256) by {
        assert(x < 65536);
    }
    assert((x / 256) % 256 == x / 256);
    assert((x % 256) + (x / 256) * 256 == x) by (nonlinear_arith)
        requires 0 <= x < 65536;
}

/// Helper: LE byte reassembly roundtrips for values < 2^32
proof fn lemma_le4_roundtrip(x: int)
    requires 0 <= x < 4294967296,
    ensures from_le_4(byte_at(x, 0), byte_at(x, 1), byte_at(x, 2), byte_at(x, 3)) == x,
{
    lemma_byte_at_basics(x);
    let b0 = x % 256;
    let b1 = (x / 256) % 256;
    let b2 = (x / 65536) % 256;
    let b3 = (x / 16777216) % 256;

    // x < 2^32, so x / 16777216 < 256
    assert(x / 16777216 < 256) by (nonlinear_arith)
        requires 0 <= x < 4294967296int;
    assert(b3 == x / 16777216);

    // Reassembly: b0 + b1*256 + b2*65536 + b3*16777216 == x
    // This is the LE decomposition identity
    assert(b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 == x) by (nonlinear_arith)
        requires
            b0 == x % 256,
            b1 == (x / 256) % 256,
            b2 == (x / 65536) % 256,
            b3 == x / 16777216,
            0 <= x < 4294967296int;
}

// ============================================================================
// Main roundtrip proof
// ============================================================================

/// Proof: compact encoding roundtrips for all u32 values
pub proof fn lemma_compact_roundtrip(val: u32)
    ensures
        compact_decode(compact_encode(val)) == Some((val, compact_encoded_len(val))),
{
    let v = val as int;
    let encoded = compact_encode(val);
    lemma_pow2_values();
    reveal(pow2);

    if val <= 63 {
        // Single-byte mode: encoded = [(v*4) as u8]
        assert(encoded.len() == 1);
        let byte0 = encoded[0];
        assert(byte0 == (v * 4) as u8);

        // v*4 <= 252 < 256, so (v*4) as u8 == v*4
        assert(0 <= v * 4 < 256) by (nonlinear_arith)
            requires 0 <= v <= 63;
        assert(byte0 as int == v * 4);

        // mode = byte0 % 4 = (v*4) % 4 = 0
        assert((v * 4) % 4 == 0) by (nonlinear_arith)
            requires 0 <= v;

        // decoded = byte0 / 4 = (v*4) / 4 = v
        assert((v * 4) / 4 == v) by (nonlinear_arith)
            requires 0 <= v;

    } else if val <= 16383 {
        // Two-byte mode: encoded_int = v*4 + 1
        let encoded_int = v * 4 + 1;
        assert(encoded.len() == 2);

        // encoded_int fits in 16 bits: max = 16383*4+1 = 65533 < 65536
        assert(0 <= encoded_int && encoded_int < 65536);

        // Get bytes
        let byte0 = encoded[0];
        let byte1 = encoded[1];
        assert(byte0 == byte_at(encoded_int, 0));
        assert(byte1 == byte_at(encoded_int, 1));

        // mode = byte0 % 4
        // byte0 = encoded_int % 256, so byte0 % 4 = encoded_int % 4 = (v*4+1) % 4 = 1
        lemma_byte_at_basics(encoded_int);
        assert(byte0 as int == encoded_int % 256);

        assert(encoded_int % 4 == 1) by (nonlinear_arith)
            requires 0 <= v, encoded_int == v * 4 + 1;
        assert((encoded_int % 256) % 4 == 1) by (nonlinear_arith)
            requires encoded_int % 4 == 1, 0 <= encoded_int < 65536;
        assert((byte0 as int) % 4 == 1);

        // decoded = from_le_2(byte0, byte1) / 4 = encoded_int / 4 = v
        lemma_le2_roundtrip(encoded_int);
        assert(from_le_2(byte0, byte1) == encoded_int);
        assert(encoded_int / 4 == v) by (nonlinear_arith)
            requires encoded_int == v * 4 + 1, 64 <= v <= 16383;

    } else if val <= 1073741823 {
        // Four-byte mode: encoded_int = v*4 + 2
        let encoded_int = v * 4 + 2;
        assert(encoded.len() == 4);

        // encoded_int fits in 32 bits: max = 1073741823*4+2 = 4294967294 < 2^32
        assert(0 <= encoded_int && encoded_int < 4294967296int);

        let byte0 = encoded[0];
        let byte1 = encoded[1];
        let byte2 = encoded[2];
        let byte3 = encoded[3];
        assert(byte0 == byte_at(encoded_int, 0));
        assert(byte1 == byte_at(encoded_int, 1));
        assert(byte2 == byte_at(encoded_int, 2));
        assert(byte3 == byte_at(encoded_int, 3));

        // mode = byte0 % 4 = encoded_int % 4 = 2
        lemma_byte_at_basics(encoded_int);
        assert(byte0 as int == encoded_int % 256);
        assert(encoded_int % 4 == 2) by (nonlinear_arith)
            requires 0 <= v, encoded_int == v * 4 + 2;
        assert((encoded_int % 256) % 4 == 2) by (nonlinear_arith)
            requires encoded_int % 4 == 2, 0 <= encoded_int < 4294967296int;
        assert((byte0 as int) % 4 == 2);

        // decoded = from_le_4(byte0..byte3) / 4 = encoded_int / 4 = v
        lemma_le4_roundtrip(encoded_int);
        assert(from_le_4(byte0, byte1, byte2, byte3) == encoded_int);
        assert(encoded_int / 4 == v) by (nonlinear_arith)
            requires encoded_int == v * 4 + 2, 16384 <= v <= 1073741823;

    } else {
        // Big-integer mode: val > 1073741823
        // encoded = [0x03, byte_at(v,0), byte_at(v,1), byte_at(v,2), byte_at(v,3)]
        assert(encoded.len() == 5);
        let byte0 = encoded[0];
        assert(byte0 == 0x03u8);

        // mode = 3 % 4 = 3
        assert((byte0 as int) % 4 == 3);

        // byte_count = byte0 / 4 + 4 = 0 + 4 = 4
        assert((byte0 as int) / 4 == 0);

        // Reconstructed value
        let byte1 = encoded[1];
        let byte2 = encoded[2];
        let byte3 = encoded[3];
        let byte4 = encoded[4];
        assert(byte1 == byte_at(v, 0));
        assert(byte2 == byte_at(v, 1));
        assert(byte3 == byte_at(v, 2));
        assert(byte4 == byte_at(v, 3));

        // v fits in u32: 0 <= v < 2^32
        assert(0 <= v < 4294967296int);

        lemma_le4_roundtrip(v);
        assert(from_le_4(byte1, byte2, byte3, byte4) == v);
    }
}

/// Proof: compact_encode produces the expected number of bytes
pub proof fn lemma_compact_encode_len(val: u32)
    ensures
        compact_encode(val).len() == compact_encoded_len(val),
{
}

/// Proof: compact_decode ignores trailing bytes.
pub proof fn lemma_compact_decode_prefix(val: u32, suffix: Seq<u8>)
    ensures
        compact_decode(compact_encode(val) + suffix)
            == compact_decode(compact_encode(val)),
{
    let enc = compact_encode(val);
    let combined = enc + suffix;
    lemma_compact_roundtrip(val);
    lemma_compact_encode_len(val);

    if val <= 63 {
        assert(combined.len() >= 1);
        assert(combined[0] == enc[0]);
    } else if val <= 16383 {
        assert(combined.len() >= 2);
        assert(combined[0] == enc[0]);
        assert(combined[1] == enc[1]);
    } else if val <= 1073741823 {
        assert(combined.len() >= 4);
        assert(combined[0] == enc[0]);
        assert(combined[1] == enc[1]);
        assert(combined[2] == enc[2]);
        assert(combined[3] == enc[3]);
    } else {
        assert(combined.len() >= 5);
        assert(combined[0] == enc[0]);
        assert(combined[1] == enc[1]);
        assert(combined[2] == enc[2]);
        assert(combined[3] == enc[3]);
        assert(combined[4] == enc[4]);
    }
}

} // verus!
