// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: known-answer tests for cSHAKE256 and FSXOF, seeded transcripts, a seed-dependence test, and enabled KAT checks

#include "random/transcript.h"

#include <sys/types.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>

#include "algebra/fp.h"
#include "algebra/static_string.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {
typedef Fp<4> Field;
static const Field F(
    "11579208921035624876269744694940757353008614341529031419553363130886709785"
    "3951");
typedef Field::Elt Elt;

// A fixed seed for the known-answer tests: bytes a0, a1, ...
template <class Hash>
BasicProofSeed<Hash> kat_seed() {
  BasicProofSeed<Hash> s;
  for (size_t i = 0; i < s.kLength; ++i) {
    s.bytes[i] = static_cast<uint8_t>(0xa0 + i);
  }
  return s;
}

// NIST cSHAKE samples (csrc.nist.gov, "cSHAKE_samples.pdf"), samples #3 and
// #4: cSHAKE256, N = "", S = "Email Signature", 512 output bits, on
// 00 01 02 03 and on 00 .. C7. Squeezed in two pieces, as the transcript
// squeezes.
void check_cshake256_sample(size_t n, const char *want_hex) {
  const char s[] = "Email Signature";
  uint8_t data[200];
  for (size_t i = 0; i < n; ++i) {
    data[i] = static_cast<uint8_t>(i);
  }
  cSHAKE_Instance x;
  ASSERT_EQ(cSHAKE256_Initialize(&x, 0, nullptr, 0,
                                 reinterpret_cast<const BitSequence *>(s),
                                 8 * (sizeof(s) - 1)),
            0);
  ASSERT_EQ(cSHAKE256_Update(&x, data, 8 * n), 0);
  ASSERT_EQ(cSHAKE256_Final(&x, nullptr), 0);
  uint8_t got[64];
  ASSERT_EQ(cSHAKE256_Squeeze(&x, got, 8 * 5), 0);
  ASSERT_EQ(cSHAKE256_Squeeze(&x, got + 5, 8 * 59), 0);
  char got_hex[129]{};
  hex_to_str(got_hex, got, sizeof(got));
  EXPECT_STREQ(got_hex, want_hex);
}

TEST(CShake256, NistSample3) {
  check_cshake256_sample(
      4, "d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1"
         "64020e2be0560858d9c00c037e34a96937c561a74c412bb4c746469527281c8c");
}

TEST(CShake256, NistSample4) {
  check_cshake256_sample(
      200, "07dc27b11e51fbac75bc7b3c1d983e8b4b85fb1defaf218912ac864302730917"
           "27f42b17ed1df63e8ec118f04b23633c1dfb1574c8fb55cb45da8e25afb092bb");
}

// FSXOF is cSHAKE256(key || seed, N = "", S = "Longfellow-FS-XOF-v1"), read
// from stream byte 0 whatever the read sizes.
TEST(Transcript, FSXOFIsCShake256) {
  uint8_t key[48], seed[48], input[96];
  for (size_t i = 0; i < sizeof(key); ++i) {
    key[i] = static_cast<uint8_t>(3 * i);
    seed[i] = static_cast<uint8_t>(5 * i + 1);
  }
  std::memcpy(input, key, sizeof(key));
  std::memcpy(input + sizeof(key), seed, sizeof(seed));
  cSHAKE_Instance x;
  ASSERT_EQ(cSHAKE256_Initialize(
                &x, 0, nullptr, 0,
                reinterpret_cast<const BitSequence *>(kFSXOFCustomization),
                8 * (sizeof(kFSXOFCustomization) - 1)),
            0);
  ASSERT_EQ(cSHAKE256_Update(&x, input, 8 * sizeof(input)), 0);
  ASSERT_EQ(cSHAKE256_Final(&x, nullptr), 0);
  uint8_t want[400];
  ASSERT_EQ(cSHAKE256_Squeeze(&x, want, 8 * sizeof(want)), 0);

  FSXOF f(key, sizeof(key), seed, sizeof(seed), 48);
  uint8_t got[400];
  f.bytes(got, 1);
  f.bytes(got + 1, 150);
  f.bytes(got + 151, 249);
  EXPECT_EQ(std::memcmp(got, want, sizeof(want)), 0);
  EXPECT_EQ(std::memcmp(f.head(), want, 48), 0);
  EXPECT_EQ(f.read(), 400u);

  // With fewer than k bytes read, head() squeezes the rest of the first k.
  FSXOF g(key, sizeof(key), seed, sizeof(seed), 48);
  g.bytes(got, 10);
  EXPECT_EQ(std::memcmp(g.head(), want, 48), 0);
}

TEST(Transcript, Write) {
  uint8_t buf1[4], buf2[4];

  Transcript ts1((uint8_t *)"test", 4, kat_seed<UpstreamHash>());
  ts1.write(F.of_scalar(7), F);
  ts1.bytes(buf1, 4);

  Transcript ts2((uint8_t *)"test", 4, kat_seed<UpstreamHash>());
  ts2.write(F.of_scalar(8), F);
  ts2.bytes(buf2, 4);

  EXPECT_NE(buf1, buf2);
}

// The seed is the write after the label and part of every XOF input: two
// transcripts that differ only in the seed differ in their keys and streams,
// and a stream is cSHAKE256 on key || seed.
TEST(Transcript, SeedChangesChallenges) {
  BasicProofSeed<SHA256> s1 = kat_seed<SHA256>();
  BasicProofSeed<SHA256> s2 = s1;
  s2.bytes[31] ^= 1;
  BasicTranscript<SHA256> t1((uint8_t *)"test", 4, s1);
  BasicTranscript<SHA256> t2((uint8_t *)"test", 4, s2);
  EXPECT_EQ(t1.seed(), s1);
  EXPECT_EQ(t1.clone().seed(), s1);
  uint8_t k1[32], k2[32], b1[16], b2[16];
  t1.get(k1);
  t2.get(k2);
  EXPECT_NE(std::memcmp(k1, k2, 32), 0);
  t1.bytes(b1, 16);
  t2.bytes(b2, 16);
  EXPECT_NE(std::memcmp(b1, b2, 16), 0);
  FSXOF x(k1, 32, s1.bytes, 32);
  uint8_t want[16];
  x.bytes(want, 16);
  EXPECT_EQ(std::memcmp(b1, want, 16), 0);
  // The seed round-trips through its serialization.
  std::vector<uint8_t> buf;
  s1.write(buf);
  EXPECT_EQ(buf.size(), 32u);
  ReadBuffer rb(buf);
  BasicProofSeed<SHA256> back;
  EXPECT_TRUE(back.read(rb));
  EXPECT_EQ(back, s1);
  EXPECT_FALSE(back.read(rb));
}

TEST(Transcript, TwoBlocks) {
  // Two consecutive squeezes of one challenge point differ.
  uint8_t a[16], b[16];
  Transcript ts((uint8_t *)"test", 4, kat_seed<UpstreamHash>());
  ts.write(F.of_scalar(8), F);
  ts.bytes(a, 16);
  ts.bytes(b, 16);
  bool same = true;
  for (size_t i = 0; i < 16; ++i) {
    same &= (a[i] == b[i]);
  }
  EXPECT_FALSE(same);
}

TEST(Transcript, Associative) {
  constexpr size_t n = 100;
  uint8_t a[n], b[n];
  for (size_t i = 0; i < n; ++i) {
    Transcript ts((uint8_t *)"test", 4, kat_seed<UpstreamHash>());
    ts.write(F.of_scalar(7), F);
    {
      Transcript ts1 = ts.clone();
      ts.bytes(a, i);
      ts.bytes(a + i, n - i);
    }
    {
      Transcript ts1 = ts.clone();
      ts1.bytes(b, n);
    }
    for (size_t j = 0; j < n; ++j) {
      EXPECT_EQ(a[j], b[j]);
    }
  }
}

void dump_elt(Elt elt) {
  uint8_t buf[Field::kBytes];
  F.to_bytes_field(buf, elt);
  for (size_t i = Field::kBytes; i-- > 0;) {
    printf("%02x", buf[i]);
  }
  printf(",\n");
}

// The known-answer vectors below fix the SHA-256 transcript digest, so they
// hold in both profiles.
using KatTranscript = BasicTranscript<SHA256>;

void check_elt_output(KatTranscript &ts, const StaticString want[/*16*/]) {
  Elt e[16];
  ts.clone().elt(e, 16, F);

  for (size_t i = 0; i < 16; ++i) {
    // Generating challenge one element at a time is equivalent to generating
    // multiple elements together.
    EXPECT_EQ(ts.elt(F), e[i]);
    EXPECT_EQ(F.of_string(want[i]), e[i]);
    dump_elt(e[i]);
  }
}

void check_nat_output(KatTranscript &ts, const size_t want[/* 24 */]) {
  size_t nat_sizes[24] = {1,   1,   1,    2,     2,     2,     7,      7,
                          7,   7,   32,   32,    32,    32,    256,    256,
                          256, 256, 1000, 10000, 60000, 65535, 100000, 100000};
  for (size_t i = 0; i < 24; ++i) {
    size_t got = ts.nat(nat_sizes[i]);
    printf("%zu ", got);
    EXPECT_EQ(got, want[i]);
  }
  printf("\n");
}

void check_choose_output(KatTranscript &ts, const size_t want[]) {
  size_t nat_sizes[6] = {31, 32, 63, 64, 1000, 65535};
  size_t got[20];

  for (size_t i = 0; i < 6; ++i) {
    ts.choose(got, nat_sizes[i], 20);
    for (size_t j = 0; j < 20; ++j) {
      EXPECT_LT(got[j], nat_sizes[i]);
      for (size_t k = 0; k < j; ++k) {
        EXPECT_NE(got[k], got[j]);
      }
      EXPECT_EQ(got[j], want[i * 20 + j]);
    }
  }
}

TEST(Transcript, TestVectors) {
  KatTranscript ts((uint8_t *)"test", 4, kat_seed<SHA256>(), 4);
  // write a byte array
  uint8_t d[100];
  for (size_t i = 0; i < 100; ++i) {
    d[i] = static_cast<uint8_t>(i);
  }
  ts.write(d, 100);

  StaticString want[16] = {
      StaticString(
          "0xaf7ef77e6b5e214fe10c3277e4a94b6ad434423f160f57c6ac94090b4d1b15f4"),
      StaticString(
          "0xe6c7e29b37663509bef77aff57f096e78917e3b86ea1d3c30cee74ed56c9e283"),
      StaticString(
          "0x1026b54e51f92593703f6ea95645899f818b6222beae44e766e1d70f51b3dfd9"),
      StaticString(
          "0x8d16c49a390d6a688b92889712acb2ce178aa4b1d0d42c127cd1c682a2f4ca54"),
      StaticString(
          "0x4574729c1226b1deaccb6e067f3f5352f4fee997f9665fb9d21f0ecb51c4a6e4"),
      StaticString(
          "0xf5ef50b1f106e528cb1e22e4b237ae2a5e5cadf4f7e4d94c1ae4c59b0c115293"),
      StaticString(
          "0xea8606cd62a37a75820007437de13f3ab54e1967ad242d1025ef0a38c417c8c0"),
      StaticString(
          "0x420875d31b08901c9900fc8615cfb48ded8cad9dec66c1f082faf34c6d1669c0"),
      StaticString(
          "0xcb6ef214f3165036a236da447139bd16e4fce83513dfad2403e2407449e12b0e"),
      StaticString(
          "0xaa65c5a490761074ebcc5689fbf793c1c57291e960b827dc12536531d2479eeb"),
      StaticString(
          "0x06aae2f10f14344bd1b1ac9b4db3458b0c160f0fc90e18aff65cf540ddce0f90"),
      StaticString(
          "0xa863ee676225b94ffcd90d5feb96656e0ae2c2af35514046ea396650bcd004ba"),
      StaticString(
          "0x318fef239f2da5c2dd641f07e618bcdcb8fe7861a1b261f8ee73c15bc523935a"),
      StaticString(
          "0x5defd596a7b0100505b6856fcbcc3c4a062412073cf63b732fceb1aca0e92bdf"),
      StaticString(
          "0x636d3d2d882f93c7d4aeaa66af71b1df8d5840c14bed1bbbb1a11e0b1090d240"),
      StaticString(
          "0x5c797f8bd6e98354f2dd54ee11017d78172868776b89ecd9d1ce3b2af419cab0"),
  };

  check_elt_output(ts, want);

  // write a field element
  ts.write(F.of_scalar(7), F);
  StaticString want2[16] = {
      StaticString(
          "0x3f88f8399d5859dad9f54652c9ea8c74037e12dd303c424af7c12b106a6b8f77"),
      StaticString(
          "0xb429508dacdb0cc54e4a11aa91c0315878ed2dff6ca3e20218da21764c9020c5"),
      StaticString(
          "0xb42ba2ae3ff7d060c4284b8c14424a493e51cb390b46b76688f66827d458eecd"),
      StaticString(
          "0x4b59998713e74d02b9cd0c1dff19e8c0dc498ca66d41373d90cff97b5349e155"),
      StaticString(
          "0xffc59ec76896a7e38ce16df5b7a356d4e1a35eff9177bcb8e16f2cb3bdacc785"),
      StaticString(
          "0x5b9ccbef4456e165a2e31f25d89ed6539fb9d002552610cca73f19f965970dd0"),
      StaticString(
          "0x53158f7a345577f05ca68455ce1a3b36319e4137d86d14844da99263fba1d905"),
      StaticString(
          "0x3732fea72fa7bb7ebd627ada9d75632dfcee0531dde99eec73fc6917b747dcdb"),
      StaticString(
          "0xf4ad853741e77bc52db2272988ba353266f6a41adc9f00cb4b900ee7a78f709c"),
      StaticString(
          "0x114bb964a2dbed3e38a2f6423e64ae1757a6360157a79ae916a2ed831379fa6e"),
      StaticString(
          "0xe0205a97f236943501a62529f0d93a245eaabb63f1034f31b7f7840c854fe8a9"),
      StaticString(
          "0xf5d8e77bf2fd7d95e1cd171335191adfe3ef35686407076727a63625c55c55dd"),
      StaticString(
          "0xf3e635f6cc5dae739c6270756100a0b8d3a06a378ed68a514407872e28d4eda9"),
      StaticString(
          "0x774331f03f52ad67b4bca341b918a08a8c5f13ad2d9dbc5e82b8e5027686a855"),
      StaticString(
          "0x64888d279d7438ff04b27847cf2326349f2fa90c59e8d1a16a4986bd6a6e3b1f"),
      StaticString(
          "0x9f193762facb1d94d48fafb0a95675304927903cfe7b679712f7bee39c99770f"),
  };

  check_elt_output(ts, want2);

  // write a field element array
  Elt array[2] = {F.of_scalar(8), F.of_scalar(9)};
  ts.write(array, 1, 2, F);

  StaticString want3[16] = {
      StaticString(
          "0x336deb1a91d86ac4f9a5144783dc4a5cf7010e8b9f7e7b791d878dfdc213eead"),
      StaticString(
          "0x3f4a5001f9bfd2f311c6d4787d56c0463f0d151a2ed09bb879a97256891b1e94"),
      StaticString(
          "0xd5091679a8f94842a3c0b9918d116ddb6b9b8f79ded3995335a83103d0a2c2dc"),
      StaticString(
          "0x6ab517744aafbfa00d58a670579332ae50b2e163202f0dc52397e2124cd9d05d"),
      StaticString(
          "0xa672ca094fa0c68ab426b3f049645c5b9583df7a9c4ace12175aed2832ae5082"),
      StaticString(
          "0x00ac76d25d2971ef79b17b8bf0958062f6740d94dcac95e65b3e8fd07f591dce"),
      StaticString(
          "0x1688621555d5ce709716c6c9871c987ea8fb78e29acacd6d93048bc1d5aeb3a9"),
      StaticString(
          "0x2a6b092e834fcc55fbbacd6f0b476adde76c1906da33f690c9063c7fb716b95e"),
      StaticString(
          "0x7f140c4794cee583ddee50adc4caf5997d047a3c1389880afed67219d6d4e1bc"),
      StaticString(
          "0x32aa4cf5ea4403f8929f2b23e998d972d7a285d70bb01c32fa8a2d5105d59d3d"),
      StaticString(
          "0x9a10c22b7a6aecf16a95aa21aceda7caef9b8e8fa3872084ca434771def43a67"),
      StaticString(
          "0x167f1c30d5cf15aeee7c55ddad786acb781bd32f1980c633fee3f6f65d113a5d"),
      StaticString(
          "0x2b8532edf682be28ed1eafa20a2e2bcd70328922be6af09f0cfa0990196a001a"),
      StaticString(
          "0xcf167bd9c71b5a50079277e2d8ce88eb5282744b0a66c4865e38c48548655c6c"),
      StaticString(
          "0xe55b27337e98768489d665e848ec0273df26c7085036f8355f94172522dd0ced"),
      StaticString(
          "0xfbe9017d352d1ee8408d7c0c16f9c3cea454efe1eb8128c03e477c4e23de5f8d"),
  };
  check_elt_output(ts, want3);

  ts.write((uint8_t *)"nats", 4);

  size_t want_nat[] = {0, 0, 0, 1, 1, 0, 4, 4, 6, 4, 1, 16,
                       1, 30, 146, 204, 130, 209, 764, 4185, 49214, 62431, 96422, 13208};
  check_nat_output(ts, want_nat);

  ts.write((uint8_t *)"choose", 6);

  size_t want_ch[] = {
      /* 31 */
      28, 11, 1, 4, 30, 7, 8, 25, 21, 15, 3, 10, 13, 19, 23, 29, 24, 12, 5, 0,
      /* 32 */
      12, 1, 8, 5, 31, 24, 28, 29, 30, 27, 14, 4, 20, 13, 9, 22, 15, 23, 3, 6,
      /* 63 */
      9, 36, 45, 60, 11, 37, 42, 0, 31, 5, 50, 13, 39, 51, 24, 44, 14, 30, 43, 46,
      /* 64 */
      42, 51, 48, 9, 10, 7, 26, 47, 19, 25, 20, 37, 60, 45, 46, 1, 56, 21, 16, 30,
      /* 1000 */
      468, 725, 69, 608, 17, 781, 601, 128, 770, 284, 603, 646, 0, 686, 811, 194, 162, 959, 536, 878,
      /* 65535 */
      57025, 15152, 47039, 51563, 24712, 12432, 13289, 113, 32892, 48885, 17270, 45030, 48296, 59378, 29132, 16666, 65126, 7008, 52269, 26290,
  };
  check_choose_output(ts, want_ch);
}

// The vectors are computed with an independent Python model: hashlib's
// SHA-256 and SHA-384 of the transcript encoding, and a pure-Python Keccak
// cSHAKE256 (checked against NIST sample 3 and against the vectors of the
// unseeded transcript) for cSHAKE256(key || seed, N = "", S =
// "Longfellow-FS-XOF-v1"), with the seed a0 a1 ... of kat_seed.
TEST(Transcript, TestVec) {
  uint8_t key[32];

  BasicTranscript<SHA256> ts((uint8_t *)"test", 4, kat_seed<SHA256>());
  uint8_t d[100];
  for (size_t i = 0; i < 100; ++i) {
    d[i] = static_cast<uint8_t>(i);
  }
  ts.write(d, 100);
  ts.get(key);

  // manually computed SHA256 of
  //    0
  //    4 0 0 0 0 0 0 0
  //    t e s t
  //    0
  //    32 0 0 0 0 0 0 0
  //    a0 a1 ... bf        // the seed
  //    0                   // TAG
  //    100 0 0 0 0 0 0 0   // LENGTH
  //    0 1 2 ...           // PAYLOAD
  {
    const uint8_t key1[32] = {0x6d, 0x34, 0x3c, 0xa6, 0xc0, 0xf2, 0xed, 0x7f,
                              0xb7, 0xbd, 0xbe, 0x05, 0x39, 0xc7, 0xaa, 0x2f,
                              0x38, 0x48, 0x6c, 0x24, 0x80, 0x11, 0x4f, 0x6b,
                              0x95, 0x86, 0x5b, 0x92, 0xde, 0x07, 0x0b, 0x1b};
    for (size_t i = 0; i < 32; ++i) {
      EXPECT_EQ(key[i], key1[i]);
    }
  }

  {
    // two squeezes of the one XOF of this challenge point
    uint8_t bytes[32];
    ts.bytes(bytes, 7);
    ts.bytes(bytes + 7, 25);

    const uint8_t bytes1[32] = {0xf4, 0x15, 0x1b, 0x4d, 0x0b, 0x09, 0x94, 0xac,
                                0xc6, 0x57, 0x0f, 0x16, 0x3f, 0x42, 0x34, 0xd4,
                                0x6a, 0x4b, 0xa9, 0xe4, 0x77, 0x32, 0x0c, 0xe1,
                                0x4f, 0x21, 0x5e, 0x6b, 0x7e, 0xf7, 0x7e, 0xaf};
    for (size_t i = 0; i < 32; ++i) {
      EXPECT_EQ(bytes[i], bytes1[i]);
    }
  }

  // append another zero; the write first absorbs the write-back
  //    3 32 0 0 0 0 0 0 0 (the first 32 stream bytes)
  ts.write(d, 1);
  ts.get(key);

  {
    const uint8_t key1[32] = {0xdf, 0x81, 0xa8, 0x0e, 0xc1, 0x08, 0x15, 0xf0,
                              0xd3, 0x0b, 0x0e, 0xa6, 0x53, 0xf3, 0x7a, 0x01,
                              0x1b, 0x09, 0x2c, 0x21, 0x68, 0xb4, 0x1c, 0xd2,
                              0xac, 0xf0, 0x14, 0xb2, 0x4f, 0x65, 0x2b, 0x32};
    for (size_t i = 0; i < 32; ++i) {
      EXPECT_EQ(key[i], key1[i]);
    }
  }
}

TEST(Transcript, Sha384TestVec) {
  BasicTranscript<SHA384> ts(reinterpret_cast<const uint8_t *>("test"), 4,
                             kat_seed<SHA384>());
  uint8_t input[100];
  for (size_t i = 0; i < 100; ++i)
    input[i] = static_cast<uint8_t>(i);
  ts.write(input, sizeof(input));
  uint8_t key[SHA384::kDigestSize];
  ts.get(key);
  char key_hex[2 * SHA384::kDigestSize + 1]{};
  hex_to_str(key_hex, key, sizeof(key));
  EXPECT_STREQ(key_hex, "29183cbdd265ccd032bc40aac513cc51dd83a35facd37152d235d7"
                        "a6c1fd3656882d1a8cdc8b0b8532999f81c1b528ce");
  uint8_t stream[64];
  ts.bytes(stream, sizeof(stream));
  char stream_hex[129]{};
  hex_to_str(stream_hex, stream, sizeof(stream));
  EXPECT_STREQ(
      stream_hex,
      "1502a60375a54bb1540db30da799dd47a346d4949e65cce567ff8c0daf04cf656f9bb86e"
      "eeac23ad658677517f4d0b66af9e02494f0be33aa83462f7ea35ae07");
  // The next write absorbs 3 || u64le(48) || the first 48 stream bytes.
  const uint8_t zero = 0;
  ts.write(&zero, 1);
  ts.get(key);
  hex_to_str(key_hex, key, sizeof(key));
  EXPECT_STREQ(key_hex, "03fd826ccd77d086845b51419dc568cf14e83a6bbc605c7d5f"
                        "b06d24e31ee0a37560255c2761c54b0c902f21bbcb7b95");
}

// A write ends the challenge point: the next squeeze starts a fresh XOF on
// the new digest, and a clone restarts the XOF of the same digest.
TEST(Transcript, WriteResetsXOF) {
  KatTranscript ts((uint8_t *)"test", 4, kat_seed<SHA256>());
  uint8_t d[100];
  for (size_t i = 0; i < 100; ++i) {
    d[i] = static_cast<uint8_t>(i);
  }
  ts.write(d, 100);
  uint8_t first[16];
  ts.bytes(first, 16);
  KatTranscript c = ts.clone();
  uint8_t again[16];
  c.bytes(again, 16);
  EXPECT_EQ(std::memcmp(first, again, 16), 0);
  ts.write(d, 1);
  uint8_t digest[32];
  ts.get(digest);
  uint8_t after[16];
  ts.bytes(after, 16);
  const BasicProofSeed<SHA256> seed = kat_seed<SHA256>();
  FSXOF x(digest, sizeof(digest), seed.bytes, seed.kLength);
  uint8_t want[16];
  x.bytes(want, 16);
  EXPECT_EQ(std::memcmp(after, want, 16), 0);
  EXPECT_NE(std::memcmp(after, first, 16), 0);
}

// The write-back: the write after a challenge point first absorbs
// 3 || u64le(k) || the first k bytes of the point's stream, which are also
// the first k bytes its challenges read. A point with no reads absorbs
// nothing.
template <class Hash>
void check_write_back() {
  constexpr size_t k = Hash::kDigestSize;
  const uint8_t label[4] = {'t', 'e', 's', 't'};
  const uint8_t msg[3] = {7, 8, 9};
  auto bstr = [](Hash &h, const uint8_t *p, size_t n) {
    uint8_t hdr[9];
    hdr[0] = 0;
    u64_to_le(hdr + 1, n);
    h.Update(hdr, 9);
    h.Update(p, n);
  };

  const BasicProofSeed<Hash> seed = kat_seed<Hash>();
  BasicTranscript<Hash> ts(label, 4, seed);
  uint8_t key[k];
  ts.get(key);
  FSXOF x(key, k, seed.bytes, k, k);
  uint8_t head[k];
  std::memcpy(head, x.head(), k);

  // Reads start at stream byte 0, so the head is what the challenges read.
  uint8_t read[k + 5];
  ts.bytes(read, 3);
  ts.bytes(read + 3, k + 2);
  EXPECT_EQ(std::memcmp(read, head, k), 0);
  uint8_t rest[k + 5];
  FSXOF x2(key, k, seed.bytes, k, k);
  x2.bytes(rest, k + 5);
  EXPECT_EQ(std::memcmp(read, rest, k + 5), 0);

  ts.write(msg, 3);
  uint8_t got[k];
  ts.get(got);

  Hash want_h;
  bstr(want_h, label, 4);
  bstr(want_h, seed.bytes, k);
  uint8_t wb[9];
  wb[0] = 3;
  u64_to_le(wb + 1, k);
  want_h.Update(wb, 9);
  want_h.Update(head, k);
  bstr(want_h, msg, 3);
  uint8_t want[k];
  want_h.DigestData(want);
  EXPECT_EQ(std::memcmp(got, want, k), 0);

  // Without the challenge point the key differs.
  Hash plain_h;
  bstr(plain_h, label, 4);
  bstr(plain_h, seed.bytes, k);
  bstr(plain_h, msg, 3);
  uint8_t plain[k];
  plain_h.DigestData(plain);
  EXPECT_NE(std::memcmp(got, plain, k), 0);

  // Two writes with no challenge between them absorb no write-back.
  BasicTranscript<Hash> ts2(label, 4, seed);
  ts2.write(msg, 3);
  ts2.get(got);
  EXPECT_EQ(std::memcmp(got, plain, k), 0);
}

TEST(Transcript, WriteBackSha256) { check_write_back<SHA256>(); }
TEST(Transcript, WriteBackSha384) { check_write_back<SHA384>(); }

// The stream budget: a point may read fs_stream_budget<Hash>() = k + e bytes.
// One more byte marks the transcript exhausted, for good.
TEST(Transcript, StreamBudget) {
  EXPECT_EQ(fs_stream_budget<SHA256>(), 32 + kFSStreamExtraBytes);
  EXPECT_EQ(fs_stream_budget<SHA384>(), 48 + kFSStreamExtraBytes);

  KatTranscript ts((uint8_t *)"test", 4, kat_seed<SHA256>());
  ts.set_stream_budget(40);
  uint8_t buf[41];
  ts.bytes(buf, 40);
  EXPECT_FALSE(ts.exhausted());
  // A fresh point has a fresh budget.
  ts.write(buf, 1);
  ts.bytes(buf, 40);
  EXPECT_FALSE(ts.exhausted());
  ts.bytes(buf, 1);
  EXPECT_TRUE(ts.exhausted());
  ts.write(buf, 1);
  EXPECT_TRUE(ts.exhausted());
  EXPECT_TRUE(ts.clone().exhausted());

  // Rejection sampling overruns: choose() needs at least 2 * 20 bytes here.
  KatTranscript tc((uint8_t *)"test", 4, kat_seed<SHA256>());
  tc.set_stream_budget(39);
  size_t idx[20];
  tc.choose(idx, 1000, 20);
  EXPECT_TRUE(tc.exhausted());

  // The protocol budget holds the largest honest points of the tests above.
  KatTranscript th((uint8_t *)"test", 4, kat_seed<SHA256>());
  th.choose(idx, 65535, 20);
  Elt e[16];
  th.elt(e, 16, F);
  EXPECT_FALSE(th.exhausted());
}

// extend_point_budget grants the open point (or the next one) more stream,
// until it closes; the stream itself does not change.
TEST(Transcript, PointBudgetExtension) {
  uint8_t buf[100], plain[100];
  KatTranscript tp((uint8_t *)"test", 4, kat_seed<SHA256>());
  tp.bytes(plain, 100);

  KatTranscript ts((uint8_t *)"test", 4, kat_seed<SHA256>());
  ts.set_stream_budget(40);
  // Granted before the point opens.
  ts.extend_point_budget(60);
  ts.bytes(buf, 100);
  EXPECT_FALSE(ts.exhausted());
  EXPECT_EQ(std::memcmp(buf, plain, 100), 0);
  // The next point has the budget alone.
  ts.write(buf, 1);
  ts.bytes(buf, 40);
  EXPECT_FALSE(ts.exhausted());
  // Granted to the open point.
  ts.extend_point_budget(10);
  ts.bytes(buf, 10);
  EXPECT_FALSE(ts.exhausted());
  ts.bytes(buf, 1);
  EXPECT_TRUE(ts.exhausted());

  // The grant for N elements covers them.
  KatTranscript te((uint8_t *)"test", 4, kat_seed<SHA256>());
  te.set_stream_budget(0);
  te.extend_point_budget_for(16, F);
  Elt e[16];
  te.elt(e, 16, F);
  EXPECT_FALSE(te.exhausted());
}
} // namespace
} // namespace proofs
