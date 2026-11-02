module

public import Rule30Open.Foundations.Evolve
public import Ruliology.CellularAutomata.Rule30EtherThree

/-!
# Beside a center column repeating a block, column 1 at one white step avoids a list of words

For each block below, let the center column repeat it and look at the right half it drives (the kit's
`Rule30Ether.drv`), from any initial right half, finite or not. At one white step of each period column 1
never reads a word of the block's list once the last reading of the word is at the block's largest rank or
later.

* `readings_00011`, `readings_00011_evolve`: `00011` at the first white step (phase 0), no `00`, `01010` from reading 5
  on; width 7, ranks at most 28.
* `readings_00101`, `readings_00101_evolve`: `00101` at the first white step (phase 0), no `010`, `101`, `1111` from
  reading 1 on; width 6, ranks at most 15.
* `readings_00111`, `readings_00111_evolve`: `00111` at the first white step (phase 0), no `11`, `1001` from reading 4
  on; width 8, ranks at most 22.
* `readings_01011`, `readings_01011_evolve`: `01011` at the second white step (phase 2), no `11` from reading 0 on;
  width 2, ranks at most 5.
* `readings_000001`, `readings_000001_evolve`: `000001` at the first white step (phase 0), no `11`, `101` from reading 2
  on; width 7, ranks at most 14.
* `readings_000011`, `readings_000011_evolve`: `000011` at the first white step (phase 0), no `010`, `101110` from
  reading 4 on; width 7, ranks at most 31.
* `readings_000111`, `readings_000111_evolve`: `000111` at the first white step (phase 0), no `11`, `101`, `1001` from
  reading 4 on; width 8, ranks at most 26.
* `readings_001101`, `readings_001101_evolve`: `001101` at the first white step (phase 0), no `11`, `101` from reading 2
  on; width 6, ranks at most 18.
* `readings_010111`, `readings_010111_evolve`: `010111` at the first white step (phase 0), no `111`, `1101` from reading
  2 on; width 6, ranks at most 22.
* `readings_0000001`, `readings_0000001_evolve`: `0000001` at the third white step (phase 2), no `00`, `0110` from
  reading 5 on; width 10, ranks at most 37.
* `readings_0000101`, `readings_0000101_evolve`: `0000101` at the fifth white step (phase 5), no `11` from reading 1 on;
  width 6, ranks at most 8.
* `readings_0001001`, `readings_0001001_evolve`: `0001001` at the first white step (phase 0), no `11` from reading 4 on;
  width 9, ranks at most 34.
* `readings_0001011`, `readings_0001011_evolve`: `0001011` at the first white step (phase 0), no `101`, `1001`, `10001`
  from reading 5 on; width 9, ranks at most 45.
* `readings_0011011`, `readings_0011011_evolve`: `0011011` at the first white step (phase 0), no `000`, `00111` from
  reading 7 on; width 10, ranks at most 59.
* `readings_0110111`, `readings_0110111_evolve`: `0110111` at the first white step (phase 0), no `11`, `101` from
  reading 4 on; width 10, ranks at most 35.

Each block has the certificate of `Rule30Open.Columns.Runs00001` in the namespace `ReadingWords.B<block>`
(`rankTabs`, `nodeOK`, `ok_p`, `parts_ok`, `rank_bound`, `no_bad`, `suf_period`, `evolve_eq_drv`) and its headline
theorems in `Rule30Open`: `no_<word>_time_<block>` by times, `readings_<block>` by readings and
`readings_<block>_evolve` for every row whose center column repeats the block.

The natural-language argument is `ReadingWords.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Rule30Ether Rule30EtherThree Rule30StripCertificates

/-! ## Block `00011` -/

section B00011

/-! The certificate and the helpers live in `ReadingWords.B00011`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B00011

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `16 * p + s` packs the rank of window `w` in bits `5 w .. 5 w + 4`. -/
def rankTabs : List Nat := [
  0x41a8041500401054060040680401004150041a004060041500401004060540100401804010041a0041a8041500401054060040680401004150041a004068040105401004060040180401804010041a,
  0x2c1a0001502c000540602c0600000000150001a02c060001502c0002c060540b000000000b0001a02c1a0001502c000540602c0600000000150001a02c06000000540b02c0602c00000000000b0001a,
  0x41a8041530401054060040680401304150041a004063041530401004063540130401804010041a0041a8041530401054060040680401304150041a004068040135401004063040180401804010041a,
  0x1a0001500000054060000600000000150001a000060001500000000060540000000000000001a0001a0001500000054060000600000000150001a000060000005400000060000000000000000001a,
  0x41a8041500401054060040680401004150041a004060041500401004060540100401804010041a0041a8041500401054060040680401004150041a004068040105401004060040180401804010041a,
  0x2c1a0041502c010540602c0600401004150041a02c060041502c0102c060540b004010040b0041a02c1a0041502c010540602c0600401004150041a02c06004010540b02c0602c01004010040b0041a,
  0x41a8041500401054060040680401004150041a004060041500401004060540100401804010041a0041a8041500401054060040680401004150041a004068040105401004060040180401804010041a,
  0x1a0001500000054060000600000000150001a000060001500000000060540000000000000001a0001a0001500000054060000600000000150001a000060000005400000060000000000000000001a,
  0x41a8041500401054060040680401004150041a004060041500401004060540100401804010041a0041a8041500401054060040680401004150041a004068040105401004060040180401804010041a,
  0x2c1a0001502c000540602c0600000000150001a02c060001502c0002c060540b000000000b0001a02c1a0001502c000540602c0600000000150001a02c06000000540b02c0602c00000000000b0001a,
  0x41a8041530401054060040680401304150041a004063041530401004063540130401804010041a0041a8041530401054060040680401304150041a004068040135401004063040180401804010041a,
  0x1a0001500000054060000600000000150001a000060001500000000060540000000000000001a0001a0001500000054060000600000000150001a000060000005400000060000000000000000001a,
  0x41a8041500401054060040680401004150041a004060041500401004060540100401804010041a0041a8041500401054060040680401004150041a004068040105401004060040180401804010041a,
  0x2c1a0001502c000540602c0600000000150001a02c060001502c0002c060540b000000000b0001a02c1a0001502c000540602c0600000000150001a02c06000000540b02c0602c00000000000b0001a,
  0x41a8041500401054060040680401004150041a004060041500401004060540100401804010041a0041a8041500401054060040680401004150041a004068040105401004060040180401804010041a,
  0x1a0001500000054060000600000000150001a000060001500000000060540000000000000001a0001a0001500000054060000600000000150001a000060000005400000060000000000000000001a,
  0x64a500014a14b9a0000014a5014000141905000014a500014014aa00014014a5016800641905000064a500014a14b9a0000014a50140001419a0000014a500014014aa00014014a50641401699,
  0x640f0000003c1900000001e000000000190000003c0f0000003c0a00000000000000006419000000640f0000003c1900000001e0000000001900000001e00000003c0a00000001e00640000019,
  0x52940064a502954a14b9a2940014a50154a5141955000014a500154514aa00154014a50168a5655955140064a502954a14b9a2940014a50154a51419a2940014a500154514aa02954014a50655451699,
  0x64000000000019000000000000000000190000000000000000000a0000000000000000641900000064000000000019000000000000000000190000000000000000000a00000000000640000019,
  0x64a500014a14b9a0000014a5014000141905000014a500014014aa00014014a5016800641905000064a500014a14b9a0000014a50140001419a0000014a500014014aa00014014a50641401699,
  0x64af0000003cb900000015e501400014190000003caf0000003caa00000014a5014000641900000064af0000003cb900000015e5014000141900000015e50000003caa00000015e50640001419,
  0x64a500014a14b9a0000014a5014000141905000014a500014014aa00014014a5016800641905000064a500014a14b9a0000014a50140001419a0000014a500014014aa00014014a50641401699,
  0x64000000000019000000000000000000190000000000000000000a0000000000000000641900000064000000000019000000000000000000190000000000000000000a00000000000640000019,
  0x64a500014a14b9a0000014a5014000141905000014a500014014aa00014014a5016800641905000064a500014a14b9a0000014a50140001419a0000014a500014014aa00014014a50641401699,
  0x640f0000003c1900000001e000000000190000003c0f0000003c0a00000000000000006419000000640f0000003c1900000001e0000000001900000001e00000003c0a00000001e00640000019,
  0x52940064a502954a14b9a2940014a50154a5141955000014a500154514aa00154014a50168a5655955140064a502954a14b9a2940014a50154a51419a2940014a500154514aa02954014a50655451699,
  0x64000000000019000000000000000000190000000000000000000a0000000000000000641900000064000000000019000000000000000000190000000000000000000a00000000000640000019,
  0x64a500014a14b9a0000014a5014000141905000014a500014014aa00014014a5016800641905000064a500014a14b9a0000014a50140001419a0000014a500014014aa00014014a50641401699,
  0x640f0000003c1900000001e000000000190000003c0f0000003c0a00000000000000006419000000640f0000003c1900000001e0000000001900000001e00000003c0a00000001e00640000019,
  0x64a500014a14b9a0000014a5014000141905000014a500014014aa00014014a5016800641905000064a500014a14b9a0000014a50140001419a0000014a500014014aa00014014a50641401699,
  0x64000000000019000000000000000000190000000000000000000a0000000000000000641900000064000000000019000000000000000000190000000000000000000a00000000000640000019,
  0x200042000924c04000182026420018c000400278200042000924c040000420004200042000498004200042000924c04000182026420018c000400278202642001824c040000424c04c00182000400018,
  0x90000e000187000000018c00000001870000000090000e000000000e700000000e0000070000000090000e000187000000018c00000001870000000180000e0000e0000ec00180000e00018,
  0x225242000924d24000182266420018c012448278201242000924d240000422524200042000498124225242000924d24000182266420018c012448278226642001824d244800424d24c00182012448138,
  0x900000000180000000018c0000000180000000009000000000000000000000000000000000000000900000000180000000018c0000000180000000018000000000000000c00180000000018,
  0x200042000924c04000182026420018c000400278200042000924c040000420004200042000498004200042000924c04000182026420018c000400278202642001824c040000424c04c00182000400018,
  0x20004200092000e000187000420018c00040001870004200092000e000042000e700042000e0000470004200092000e000187000420018c00040001870004200182000e0000e2000ec00182000e00018,
  0x200042000924c04000182026420018c000400278200042000924c040000420004200042000498004200042000924c04000182026420018c000400278202642001824c040000424c04c00182000400018,
  0x900000000180000000018c0000000180000000009000000000000000000000000000000000000000900000000180000000018c0000000180000000018000000000000000c00180000000018,
  0x200042000924c04000182026420018c000400278200042000924c040000420004200042000498004200042000924c04000182026420018c000400278202642001824c040000424c04c00182000400018,
  0x90000e000187000000018c00000001870000000090000e000000000e700000000e0000070000000090000e000187000000018c00000001870000000180000e0000e0000ec00180000e00018,
  0x225242000924d24000182266420018c012448278201242000924d240000422524200042000498124225242000924d24000182266420018c012448278226642001824d244800424d24c00182012448138,
  0x900000000180000000018c0000000180000000009000000000000000000000000000000000000000900000000180000000018c0000000180000000018000000000000000c00180000000018,
  0x200042000924c04000182026420018c000400278200042000924c040000420004200042000498004200042000924c04000182026420018c000400278202642001824c040000424c04c00182000400018,
  0x90000e000187000000018c00000001870000000090000e000000000e700000000e0000070000000090000e000187000000018c00000001870000000180000e0000e0000ec00180000e00018,
  0x200042000924c04000182026420018c000400278200042000924c040000420004200042000498004200042000924c04000182026420018c000400278202642001824c040000424c04c00182000400018,
  0x900000000180000000018c0000000180000000009000000000000000000000000000000000000000900000000180000000018c0000000180000000018000000000000000c00180000000018,
  0xc0300c6300c0800c6300c1700c7700e5c00c6300c0300ee300c0890c7700c0800c6300c1c00c7700c0300ee300c0890c7700c1700c7700e5c00c6300c1700c7700c0890c7700c0800c7700c0800c63,
  0x1ad034080000d03417000170001c035a000000002e00340800017034080000d0001c001b700000002ed034080001703417000170001c035a00341700017034080001703408000170000800000,
  0xd0300c6300d0840c6300c1700c7700e5c40c6300c0300ee300d0890c7700d0800c6300d1c00c7700d0300ee300d0890c7700c1700c7700e5c40c6300c1700c7700d0890c7700d0800c7700d0840c63,
  0x80000000017000170001c0000000000002e0000080001700008000000001c0001700000002e0000080001700017000170001c000000001700017000080001700008000170000800000,
  0xc0300c6300c0800c6300c1700c7700e5c00c6300c0300ee300c0890c7700c0800c6300c1c00c7700c0300ee300c0890c7700c1700c7700e5c00c6300c1700c7700c0890c7700c0800c7700c0800c63,
  0xc0300dad0340800c6d0341700c7700c1c035a300c0300ee30340800c770340800c6d00c1c00db700c0300eed0340800c770341700c7700c1c035a30341700c770340800c770340800c7700c0800c63,
  0xc0300c6300c0800c6300c1700c7700e5c00c6300c0300ee300c0890c7700c0800c6300c1c00c7700c0300ee300c0890c7700c1700c7700e5c00c6300c1700c7700c0890c7700c0800c7700c0800c63,
  0x80000000017000170001c0000000000002e0000080001700008000000001c0001700000002e0000080001700017000170001c000000001700017000080001700008000170000800000,
  0xc0300c6300c0800c6300c1700c7700e5c00c6300c0300ee300c0890c7700c0800c6300c1c00c7700c0300ee300c0890c7700c1700c7700e5c00c6300c1700c7700c0890c7700c0800c7700c0800c63,
  0x1ad034080000d03417000170001c035a000000002e00340800017034080000d0001c001b700000002ed034080001703417000170001c035a00341700017034080001703408000170000800000,
  0xd0300c6300d0840c6300c1700c7700e5c40c6300c0300ee300d0890c7700d0800c6300d1c00c7700d0300ee300d0890c7700c1700c7700e5c40c6300c1700c7700d0890c7700d0800c7700d0840c63,
  0x80000000017000170001c0000000000002e0000080001700008000000001c0001700000002e0000080001700017000170001c000000001700017000080001700008000170000800000,
  0xc0300c6300c0800c6300c1700c7700e5c00c6300c0300ee300c0890c7700c0800c6300c1c00c7700c0300ee300c0890c7700c1700c7700e5c00c6300c1700c7700c0890c7700c0800c7700c0800c63,
  0x1ad034080000d03417000170001c035a000000002e00340800017034080000d0001c001b700000002ed034080001703417000170001c035a00341700017034080001703408000170000800000,
  0xc0300c6300c0800c6300c1700c7700e5c00c6300c0300ee300c0890c7700c0800c6300c1c00c7700c0300ee300c0890c7700c1700c7700e5c00c6300c1700c7700c0890c7700c0800c7700c0800c63,
  0x80000000017000170001c0000000000002e0000080001700008000000001c0001700000002e0000080001700017000170001c000000001700017000080001700008000170000800000,
  0xd8851108403884038840d8ac010840b0b6010ac0d885110ac038840388403d840b0840108e0b0840d885110ac03884038840d8ac010840b0b6010ac0d8ac0108403d840d884038840b08401084010840,
  0xd8180001803b1803b000d82c000180b0360032c0d8180002c03b0003b0003d800b0180000e0b0000d8180002c03b1803b000d82c000180b0360032c0d82c0001803d800db0003b180b01800018060000,
  0xd8851108403884738840d8ac710840b0b6010ac0d885110ac038847388403d847b0840108e0b0840d885110ac03884738840d8ac710840b0b6010ac0d8ac7108403d847d884038847b08401084710840,
  0xd8000000003800038000d82c000000b0360002c0d8000002c038000380003d800b0000000e0b0000d8000002c03800038000d82c000000b0360002c0d82c0000003d800d800038000b00000000000000,
  0xd8851108403884038840d8ac010840b0b6010ac0d885110ac038840388403d840b0840108e0b0840d885110ac03884038840d8ac010840b0b6010ac0d8ac0108403d840d884038840b08401084010840,
  0xd8980109803b1803b040d8ac010980b0b60132c0d898010ac03b0403b0403d840b0980108e0b0840d898010ac03b1803b040d8ac010980b0b60132c0d8ac0109803d840db0403b180b09801098060840,
  0xd8851108403884038840d8ac010840b0b6010ac0d885110ac038840388403d840b0840108e0b0840d885110ac03884038840d8ac010840b0b6010ac0d8ac0108403d840d884038840b08401084010840,
  0xd8000000003800038000d82c000000b0360002c0d8000002c038000380003d800b0000000e0b0000d8000002c03800038000d82c000000b0360002c0d82c0000003d800d800038000b00000000000000,
  0xd8851108403884038840d8ac010840b0b6010ac0d885110ac038840388403d840b0840108e0b0840d885110ac03884038840d8ac010840b0b6010ac0d8ac0108403d840d884038840b08401084010840,
  0xd8180001803b1803b000d82c000180b0360032c0d8180002c03b0003b0003d800b0180000e0b0000d8180002c03b1803b000d82c000180b0360032c0d82c0001803d800db0003b180b01800018060000,
  0xd8851108403884738840d8ac710840b0b6010ac0d885110ac038847388403d847b0840108e0b0840d885110ac03884738840d8ac710840b0b6010ac0d8ac7108403d847d884038847b08401084710840,
  0xd8000000003800038000d82c000000b0360002c0d8000002c038000380003d800b0000000e0b0000d8000002c03800038000d82c000000b0360002c0d82c0000003d800d800038000b00000000000000,
  0xd8851108403884038840d8ac010840b0b6010ac0d885110ac038840388403d840b0840108e0b0840d885110ac03884038840d8ac010840b0b6010ac0d8ac0108403d840d884038840b08401084010840,
  0xd8180001803b1803b000d82c000180b0360032c0d8180002c03b0003b0003d800b0180000e0b0000d8180002c03b1803b000d82c000180b0360032c0d82c0001803d800db0003b180b01800018060000,
  0xd8851108403884038840d8ac010840b0b6010ac0d885110ac038840388403d840b0840108e0b0840d885110ac03884038840d8ac010840b0b6010ac0d8ac0108403d840d884038840b08401084010840,
  0xd8000000003800038000d82c000000b0360002c0d8000002c038000380003d800b0000000e0b0000d8000002c03800038000d82c000000b0360002c0d82c0000003d800d800038000b00000000000000
]

/-! ### States, the step and the check -/

/-- The block `00011`, letter `p` at phase `p`. -/
def w00011 : List Bool := [false, false, false, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `5 w .. 5 w + 4` of table
`16 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (16 * p + s) 0 >>> (5 * w)) % 32

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `00`, `01010`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 0) ||
    ((2 * s + b.toNat) % 32 == 10)

/-- The last 4 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 16 else s

/-- The window of columns 1..7 after a step from phase `p`, with column 8 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 7 (w00011.getD p false) z w

/-- The certificate at one state: ranks are at most 28; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 5) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 5) (sNext p s w) (wNext p w true)
  decide (r ≤ 28) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 128

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 16 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 16 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 16 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 16 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 16 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 5 → allBelowT (partOK p) 16 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | p + 5, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 5) (hs : s < 16) (hw : w < 2 ^ 7) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 7 = 128 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 28 ∧
      (rk p s w = 0 → rk ((p + 1) % 5) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 5) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `00011` read from phase `ph`: letter `(t + ph) % 5` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w00011.getD ((t + ph) % 5) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..7` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 7
  | t + 1 => stripStep 7 (F t 0) (F t 8) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 7 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 7).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last four readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 5) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 16
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 16
    unfold sNext
    cases ((t + ph) % 5 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 16

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 5) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 8) := by
  show stripStep 7 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `28 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 28 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 8)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 5 = ((t + ph) % 5 + 1) % 5 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 28 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 28 ≤ t) (hp : (t + ph) % 5 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 5 = 0) :
    suf ph (drv (ctr ph) R) (t + 5) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 5) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  rw [h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_00 : ∀ s, s < 16 → badB (push s false) false = true := by decide +kernel
theorem bad_01010 : ∀ s, s < 16 → badB (push (push (push (push s false) true) false) true) false = true
    := by decide +kernel

end ReadingWords.B00011

open ReadingWords.B00011

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `00`.** At the first white steps, column 1 never reads `00` with the first reading at time `23` or
later. -/
theorem no_00_time_00011 (u : Nat) (hu : 23 ≤ u) (hp : (u + ph) % 5 = 0) :
    ¬ (drv (ctr ph) R u 1 = false ∧ drv (ctr ph) R (u + 5) 1 = false) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 5) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_00 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `01010`.** At the first white steps, column 1 never reads `01010` with the first reading at time `8` or
later. -/
theorem no_01010_time_00011 (u : Nat) (hu : 8 ≤ u) (hp : (u + ph) % 5 = 0) :
    ¬ (drv (ctr ph) R u 1 = false ∧ drv (ctr ph) R (u + 5) 1 = true ∧ drv (ctr ph) R (u + 10) 1 = false ∧
      drv (ctr ph) R (u + 15) 1 = true ∧ drv (ctr ph) R (u + 20) 1 = false) := by
  rintro ⟨h0, h1, h2, h3, h4⟩
  rw [show u + 10 = u + 5 + 5 by omega] at h2
  rw [show u + 15 = u + 5 + 5 + 5 by omega] at h3
  rw [show u + 20 = u + 5 + 5 + 5 + 5 by omega] at h4
  have hb := no_bad R ph (u + 5 + 5 + 5 + 5) (by omega) (by omega)
  rw [suf_period R ph (u + 5 + 5 + 5) (by omega), suf_period R ph (u + 5 + 5) (by omega),
    suf_period R ph (u + 5) (by omega), suf_period R ph u hp, h0, h1, h2, h3, h4] at hb
  rw [bad_01010 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B00011

/-- A sequence of bits has none of the factors `00`, `01010` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = false ∧ b (i + 1) = false) ∧
    ¬ (b i = false ∧ b (i + 1) = true ∧ b (i + 2) = false ∧ b (i + 3) = true ∧ b (i + 4) = false)

/-- Column 1 of the right half driven by `00011` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 5 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (5 * i + (5 - ph % 5) % 5) 1

end ReadingWords.B00011

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`00`, `01010` from the 5th on. -/
theorem readings_00011 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 5 := by
  intro i hi
  have hp : (5 * i + (5 - ph % 5) % 5 + ph) % 5 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 5) 1 := by
    unfold reading; rw [show 5 * (i + 1) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 5 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 10) 1 := by
    unfold reading; rw [show 5 * (i + 2) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 10 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 15) 1 := by
    unfold reading; rw [show 5 * (i + 3) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 15 by omega]
  have e4 : reading R ph (i + 4) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 20) 1 := by
    unfold reading; rw [show 5 * (i + 4) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 20 by omega]
  rw [e1, e2, e3, e4]
  exact ⟨no_00_time_00011 R ph _ (by omega) hp, no_01010_time_00011 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `00011` -/

namespace ReadingWords.B00011

/-- From time `T` on, a row whose center column repeats `00011` from `T` has the right half driven by `00011` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w00011.getD ((t - T) % 5) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w00011.getD ((0 + 0) % 5) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w00011.getD ((t + 1 + 0) % 5) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B00011

/-- **Readings of every row.** If the center column of a row repeats `00011` from time `T` (letter
`(t - T) % 5` at time `t`), then column 1 at the times `T + 5 i` avoids `00`, `01010` from `i = 5` on. -/
theorem readings_00011_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w00011.getD ((t - T) % 5) false) :
    Avoids (fun i => evolve init (T + 5 * i) 1) 5 := by
  have e : (fun i => evolve init (T + 5 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 5 * i = T + (5 * i + (5 - 0 % 5) % 5) by omega]
    exact evolve_eq_drv init T h (5 * i + (5 - 0 % 5) % 5) 1
  rw [e]
  exact readings_00011 _ 0

end B00011

/-! ## Block `00101` -/

section B00101

/-! The certificate and the helpers live in `ReadingWords.B00101`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B00101

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `8 * p + s` packs the rank of window `w` in bits `4 w .. 4 w + 3`. -/
def rankTabs : List Nat := [
  0x6060006000606060606000600060606060600060006060600060006000606060,
  0x1060101b1010101010601010101010101060101b1010101b101010101010101,
  0x6060106010606060606010601060606060601060106060601060106010606060,
  0x66000b0000000000660006000000000066000b0000000b000600060000000,
  0x6060006000606060606000600060606060600060006060600060006000606060,
  0x1060101b1010101010601010101010101060101b1010101b101010101010101,
  0x6060106010606060606010601060606060601060106060601060106010606060,
  0x10166010b0101010101660106010101010166010b0101010b010601060101010,
  0xa000000a00000000a000000a00000000a000000a00000000a000000000,
  0x55555f055555500a55555005a055505555555f055555500a5555a0055f555f5a,
  0x5a000000a50000005a005000a00000005a000000a50000005a005000500,
  0xf00000000aa00000a00aa00000000000f00000000aa0000aa000f000f0a,
  0xa000000a00000000a000000a00000000a000000a00000000a000000000,
  0x55555f055555500a55555005a055505555555f055555500a5555a0055f555f5a,
  0x5a000000a50000005a005000a00000005a000000a50000005a005000500,
  0xf50000005aa00000a50aa00050000000f50000005aa0000aa500f000f0a,
  0x9000000090000000900000000000000090000000900000009000000000000000,
  0x44404940444444404440449e444494404440499044444440444e44904444449,
  0x9000400090000000900040004000000090004000900000009000400040000000,
  0x90900000000000009009e000090000009099000000000000e00990000009,
  0x9000000090000000900000000000000090000000900000009000000000000000,
  0x44404940444444404440449e444494404440499044444440444e44904444449,
  0x9000400090000000900040004000000090004000900000009000400040000000,
  0x400090904000000040009009e000090040009099400000004000e00990000009,
  0x8000000000000000800000000000000080000000000000008,
  0x3383333d3833333033833330333333803383333d383333303833333033338330,
  0x300000008000000030000000800000003000000080000000300000008,
  0x80000d0800000000800008000000800080000d080000000800000800008000,
  0x8000000000000000800000000000000080000000000000008,
  0x3383333d3833333033833330333333803383333d383333303833333033338330,
  0x300000008000000030000000800000003000000080000000300000008,
  0x80000d0800000300800008000000830080000d080000030800000800008003,
  0x700000007000000070007000700000007000000070000000700070007,
  0x22202220222c7220222022202270222022202220222c7220222c2220227c2220,
  0x2000700020007000200070007000700020007000200070002000700070007,
  0x70000000c7000000700000070000000070000000c7000000c0000007c0000,
  0x700000007000000070007000700000007000000070000000700070007,
  0x22202220222c7220222022202270222022202220222c7220222c2220227c2220,
  0x2000700020007000200070007000700020007000200070002000700070007,
  0x70002000c7002000700020072000200070002000c7002000c0002007c0002
]

/-! ### States, the step and the check -/

/-- The block `00101`, letter `p` at phase `p`. -/
def w00101 : List Bool := [false, false, true, false, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `4 w .. 4 w + 3` of table
`8 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (8 * p + s) 0 >>> (4 * w)) % 16

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `010`, `101`, `1111`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 8 == 2) ||
    ((2 * s + b.toNat) % 8 == 5) ||
    ((2 * s + b.toNat) % 16 == 15)

/-- The last 3 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 8 else s

/-- The window of columns 1..6 after a step from phase `p`, with column 7 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 6 (w00101.getD p false) z w

/-- The certificate at one state: ranks are at most 15; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 5) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 5) (sNext p s w) (wNext p w true)
  decide (r ≤ 15) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 64

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 8 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 8 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 8 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 8 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 8 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 5 → allBelowT (partOK p) 8 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | p + 5, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 5) (hs : s < 8) (hw : w < 2 ^ 6) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 6 = 64 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 15 ∧
      (rk p s w = 0 → rk ((p + 1) % 5) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 5) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `00101` read from phase `ph`: letter `(t + ph) % 5` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w00101.getD ((t + ph) % 5) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..6` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 6
  | t + 1 => stripStep 6 (F t 0) (F t 7) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 6 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 6).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last three readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 5) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 8
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 8
    unfold sNext
    cases ((t + ph) % 5 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 8

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 5) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 7) := by
  show stripStep 6 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `15 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 15 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 7)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 5 = ((t + ph) % 5 + 1) % 5 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 15 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 15 ≤ t) (hp : (t + ph) % 5 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 5 = 0) :
    suf ph (drv (ctr ph) R) (t + 5) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 5) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  rw [h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_010 : ∀ s, s < 8 → badB (push (push s false) true) false = true := by decide
theorem bad_101 : ∀ s, s < 8 → badB (push (push s true) false) true = true := by decide
theorem bad_1111 : ∀ s, s < 8 → badB (push (push (push s true) true) true) true = true := by decide

end ReadingWords.B00101

open ReadingWords.B00101

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `010`.** At the first white steps, column 1 never reads `010` with the first reading at time `5` or
later. -/
theorem no_010_time_00101 (u : Nat) (hu : 5 ≤ u) (hp : (u + ph) % 5 = 0) :
    ¬ (drv (ctr ph) R u 1 = false ∧ drv (ctr ph) R (u + 5) 1 = true ∧ drv (ctr ph) R (u + 10) 1 = false) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 10 = u + 5 + 5 by omega] at h2
  have hb := no_bad R ph (u + 5 + 5) (by omega) (by omega)
  rw [suf_period R ph (u + 5) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_010 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `101`.** At the first white steps, column 1 never reads `101` with the first reading at time `5` or
later. -/
theorem no_101_time_00101 (u : Nat) (hu : 5 ≤ u) (hp : (u + ph) % 5 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 5) 1 = false ∧ drv (ctr ph) R (u + 10) 1 = true) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 10 = u + 5 + 5 by omega] at h2
  have hb := no_bad R ph (u + 5 + 5) (by omega) (by omega)
  rw [suf_period R ph (u + 5) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_101 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `1111`.** At the first white steps, column 1 never reads `1111` with the first reading at time `0` or
later. -/
theorem no_1111_time_00101 (u : Nat) (hu : 0 ≤ u) (hp : (u + ph) % 5 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 5) 1 = true ∧ drv (ctr ph) R (u + 10) 1 = true ∧
      drv (ctr ph) R (u + 15) 1 = true) := by
  rintro ⟨h0, h1, h2, h3⟩
  rw [show u + 10 = u + 5 + 5 by omega] at h2
  rw [show u + 15 = u + 5 + 5 + 5 by omega] at h3
  have hb := no_bad R ph (u + 5 + 5 + 5) (by omega) (by omega)
  rw [suf_period R ph (u + 5 + 5) (by omega), suf_period R ph (u + 5) (by omega), suf_period R ph u hp, h0, h1, h2,
    h3] at hb
  rw [bad_1111 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B00101

/-- A sequence of bits has none of the factors `010`, `101`, `1111` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = false ∧ b (i + 1) = true ∧ b (i + 2) = false) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = true ∧ b (i + 2) = true ∧ b (i + 3) = true)

/-- Column 1 of the right half driven by `00101` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 5 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (5 * i + (5 - ph % 5) % 5) 1

end ReadingWords.B00101

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`010`, `101`, `1111` from the 1th on. -/
theorem readings_00101 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 1 := by
  intro i hi
  have hp : (5 * i + (5 - ph % 5) % 5 + ph) % 5 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 5) 1 := by
    unfold reading; rw [show 5 * (i + 1) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 5 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 10) 1 := by
    unfold reading; rw [show 5 * (i + 2) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 10 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 15) 1 := by
    unfold reading; rw [show 5 * (i + 3) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 15 by omega]
  rw [e1, e2, e3]
  exact ⟨no_010_time_00101 R ph _ (by omega) hp, no_101_time_00101 R ph _ (by omega) hp,
    no_1111_time_00101 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `00101` -/

namespace ReadingWords.B00101

/-- From time `T` on, a row whose center column repeats `00101` from `T` has the right half driven by `00101` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w00101.getD ((t - T) % 5) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w00101.getD ((0 + 0) % 5) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w00101.getD ((t + 1 + 0) % 5) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B00101

/-- **Readings of every row.** If the center column of a row repeats `00101` from time `T` (letter
`(t - T) % 5` at time `t`), then column 1 at the times `T + 5 i` avoids `010`, `101`, `1111` from `i = 1` on. -/
theorem readings_00101_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w00101.getD ((t - T) % 5) false) :
    Avoids (fun i => evolve init (T + 5 * i) 1) 1 := by
  have e : (fun i => evolve init (T + 5 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 5 * i = T + (5 * i + (5 - 0 % 5) % 5) by omega]
    exact evolve_eq_drv init T h (5 * i + (5 - 0 % 5) % 5) 1
  rw [e]
  exact readings_00101 _ 0

end B00101

/-! ## Block `00111` -/

section B00111

/-! The certificate and the helpers live in `ReadingWords.B00111`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B00111

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `8 * p + s` packs the rank of window `w` in bits `5 w .. 5 w + 4`. -/
def rankTabs : List Nat := [
  0x8000000200000000000080000000150000000000000000000080000800000000000000000000000080000002000000000000000000000000000000008000000200000008000000000000000000000000800000020000000000008000000015000000000000000000008000080000000000000000000000000000000000000000000080000000000000000000800000000080000000000000000000,
  0xac200802082c20082000ac2008020800200803508020080200ac200802080020800200802b08020080200802082c20082000ac20080200802b080200ac200802080020082000ac208002008020080200ac200802082c20082000ac20080208002b0803508020080200ac200802080020800200802b0802008020080200ac20080200ac20080208002b080200ac200802082c200802082c20080200802008020,
  0x8000000206000000000080000000150000000000000000000680000800000000000000000000000080000002060000000000000000000600000000008000000206000008000000000000000000000000800000020600000000008000000015000000000000000000068000080000000000000000000000000000000006000000000080000000060000000000800000000680000000000000000000,
  0xac200802082c20082000ac2008020800200803508020080200ac200802080020800200802b08020080200802082c20082000ac20080200802b080200ac200802080020082000ac208002008020080200ac200802082c20082000ac20080208002b0803508020080200ac200802080020800200802b0802008020080200ac20080200ac20080208002b080200ac200802082c200802082c20080200802008020,
  0x8020080208002008200080200802080020080350802008020080200802080020800200802008020080200802080020082000802008020080200802008020080208002008200080208002008020080200802008020800200820008020080208002008035080200802008020080208002080020080200802008020080200802008020080200802080020080200802008020800200802080020080200802008020,
  0xac200802082c20082000ac2008020800200803508020080200ac200802080020800200802b08020080200802082c20082000ac20080200802b080200ac200802080020082000ac208002008020080200ac200802082c20082000ac20080208002b0803508020080200ac200802080020800200802b0802008020080200ac20080200ac20080208002b080200ac200802082c200802082c20080200802008020,
  0x8000000206000000000080000000150000000000000000000680000800000000000000000000000080000002060000000000000000000600000000008000000206000008000000000000000000000000800000020600000000008000000015000000000000000000068000080000000000000000000000000000000006000000000080000000060000000000800000000680000000000000000000,
  0xac200802082c20082000ac2008020800200803508020080200ac200802080020800200802b08020080200802082c20082000ac20080200802b080200ac200802080020082000ac208002008020080200ac200802082c20082000ac20080208002b0803508020080200ac200802080020800200802b0802008020080200ac20080200ac20080208002b080200ac200802082c200802082c20080200802008020,
  0x1400000000000000000000000000000000000000000000000000000000000000000000000000000014000000000000000000000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000014000000000000000000000000000000000000001400000000000000000000,
  0x7bde500000001e5000007bc05780000000000000001e50000000014000007bc057bc0000000000000000500000001e5000007bc0503c0003c00000007bc0500000001f400000780050000003c0f000007bde500000001e5000007bc057bc0003c0000000001e50000000014000007bc057bc000000000000001e50000000014000007bc057bc0003c00000007bc0500000001f4000007bc057bc0003c0f,
  0x2940000000014000000028000000000140500000000000000001405001400140000000000000140029400000000140000000280000000001405000002800000000014050014001400000000140000000294000000001400000002800000000014050000000000000000140500140014000000000000014000000000000014050014028000000000140500000280000000001405001400140000000014050140,
  0x7bde500000001e5000007bc05780000000000000001e50000000014000007bc057bc0000000000000000500000001e5000007bc0503c0003c00000007bc0500000001f400000780050000003c0f000007bde500000001e5000007bc057bc0003c0000000001e50000000014000007bc057bc000000000000001e50000000014000007bc057bc0003c00000007bc0500000001f4000007bc057bc0003c0f,
  0x50000000005000000000500000000000000000005000000001400000000050000000000000000000500000000050000000005000000000000000000050000000014000000000500000000000000000005000000000500000000050000000000000000000500000000140000000005000000000000000000050000000014000000000500000000000000000005000000001400000000050000000000,
  0x7bde500000001e5000007bc05780000000000000001e50000000014000007bc057bc0000000000000000500000001e5000007bc0503c0003c00000007bc0500000001f400000780050000003c0f000007bde500000001e5000007bc057bc0003c0000000001e50000000014000007bc057bc000000000000001e50000000014000007bc057bc0003c00000007bc0500000001f4000007bc057bc0003c0f,
  0x2940000000014000000028000000000140500000000000000001405001400140000000000000140029400000000140000000280000000001405000002800000000014050014001400000000140000000294000000001400000002800000000014050000000000000000140500140014000000000000014000000000000014050014028000000000140500000280000000001405001400140000000014050140,
  0x7bde500000001e5000007bc05780000000000000001e50000000014000007bc057bc0000000000000000500000001e5000007bc0503c0003c00000007bc0500000001f400000780050000003c0f000007bde500000001e5000007bc057bc0003c0000000001e50000000014000007bc057bc000000000000001e50000000014000007bc057bc0003c00000007bc0500000001f4000007bc057bc0003c0f,
  0x130000000000000000000000000000000000000013000000000000000000130001300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000013000000000000000000000000000000000000001300000000000000000013000130000000000000130000000000000000000000000000000000000000000000000000000000000000000000,
  0x4701d3700040380000004701c4000040000000004001d300004000007000400013700130000e0000470004700040380000004701c4000040380000004701c470004000000000400004000040000e00004701d3700040380000004701c4000040380000004001d300004000007000400013700130000e00004001d3000040000000004701c4000040380000004701c4700040000070004701c47000400000,
  0x120000130012000000000000000000000480000012000013001200000000120000130001300000001200000000120000000000000000000004800000000000000012000000001200000000120480000012000013001200000000000000000000048000001200001300120000000012000013000130000000120000130012000000000000000000000480000000000000001200000000120000000012048000,
  0x4701d3700040380000004701c4000040000000004001d300004000007000400013700130000e0000470004700040380000004701c4000040380000004701c470004000000000400004000040000e00004701d3700040380000004701c4000040380000004001d300004000007000400013700130000e00004001d3000040000000004701c4000040380000004701c4700040000070004701c47000400000,
  0x4000130000400000000040000400004000000000400013000040000000004000130001300000000040000400004000000000400004000040000000004000040000400000000040000400004000000000400013000040000000004000040000400000000040001300004000000000400013000130000000004000130000400000000040000400004000000000400004000040000000004000040000400000,
  0x4701d3700040380000004701c4000040000000004001d300004000007000400013700130000e0000470004700040380000004701c4000040380000004701c470004000000000400004000040000e00004701d3700040380000004701c4000040380000004001d300004000007000400013700130000e00004001d3000040000000004701c4000040380000004701c4700040000070004701c47000400000,
  0x120000130012000000000000000000000480000012000013001200000000120000130001300000001200000000120000000000000000000004800000000000000012000000001200000000120480000012000013001200000000000000000000048000001200001300120000000012000013000130000000120000130012000000000000000000000480000000000000001200000000120000000012048000,
  0x4701d3700040380000004701c4000040000000004001d300004000007000400013700130000e0000470004700040380000004701c4000040380000004701c470004000000000400004000040000e00004701d3700040380000004701c4000040380000004001d300004000007000400013700130000e00004001d3000040000000004701c4000040380000004701c4700040000070004701c47000400000,
  0x240000000024090000900000000000000000000000000000000000000000240000000024000000002400000000240900009000000000000009000000000000000024000000000000000000240000000024000000002409000090000000000000090000000000000000000000000024000000002400000000000000000000000000900000000000000900009000000000002400000000240000000024090000,
  0x1824018000182409000d934601800d1806018000180601800018060180001b6401800018240181a018240180001b6409000d934601800d18060901a01b4601800d1b6401800d180601800d182401800018240180001b6409000d934601800d18060901a0180601800018060180001b6401800018240181a018060180001806018000934601800d18060901a0934601800d1b6401800d1b6401800d1824090000,
  0x240000000024890000900000000000000000000000000000000080000000248000000024800000002400000000248900009000000000000009000000000000000024800000000080000000248000000024000000002489000090000000000000090000000000000000008000000024800000002480000000000000000000800000900000000000000900009000000000002480000000248000000024890000,
  0x1824018000182409000d934601800d1806018000180601800018060180001b6401800018240181a018240180001b6409000d934601800d18060901a01b4601800d1b6401800d180601800d182401800018240180001b6409000d934601800d18060901a0180601800018060180001b6401800018240181a018060180001806018000934601800d18060901a0934601800d1b6401800d1b6401800d1824090000,
  0x18240180001824090000900601800018060180001806018000180601800018240180001824018000182401800018240900009006018000180609000018060180001824018000180601800018240180001824018000182409000090060180001806090000180601800018060180001824018000182401800018060180001806018000900601800018060900009006018000182401800018240180001824090000,
  0x1824018000182409000d934601800d1806018000180601800018060180001b6401800018240181a018240180001b6409000d934601800d18060901a01b4601800d1b6401800d180601800d182401800018240180001b6409000d934601800d18060901a0180601800018060180001b6401800018240181a018060180001806018000934601800d18060901a0934601800d1b6401800d1b6401800d1824090000,
  0x240000000024890000900000000000000000000000000000000080000000248000000024800000002400000000248900009000000000000009000000000000000024800000000080000000248000000024000000002489000090000000000000090000000000000000008000000024800000002480000000000000000000800000900000000000000900009000000000002480000000248000000024890000,
  0x1824018000182409000d934601800d1806018000180601800018060180001b6401800018240181a018240180001b6409000d934601800d18060901a01b4601800d1b6401800d180601800d182401800018240180001b6409000d934601800d18060901a0180601800018060180001b6401800018240181a018060180001806018000934601800d18060901a0934601800d1b6401800d1b6401800d1824090000,
  0x11000000001100000000000000000000000000000000000000110000000000000000000000000000110000000000000000000000011b0011000000001100000000000000000011000000000000000000110000000011000000000000011000000000000000000000001100000000000000000000000000000000000b00110000000000000110001100000000110000000011000000001100000,
  0x20018200011030020019100182000020300200182000020000200002000110018200002600020000200182000110300200182001820000203011b0011001820001103002000020000200011600020000200182000110300200191001820000203011001820000200002000020001100182000026000200182000020000200002b01910018200002030110019100182000110000200011001820001100002,
  0x38011000003801100000000000000000000000003800000000380110000000000000000000000000380110000038000000000000000011b0011000003801100000380000000000011000000000000000380110000038011000000000000011000000000038000000003801100000000000000000000000003800000000b00110000000000000113801100000380110000038011000000001100000,
  0x20018200011030020019100182000020300200182000020000200002000110018200002600020000200182000110300200182001820000203011b0011001820001103002000020000200011600020000200182000110300200191001820000203011001820000200002000020001100182000026000200182000020000200002b01910018200002030110019100182000110000200011001820001100002,
  0x20000200011000020001100002000020000200002000020000200002000110000200002000020000200002000110000200002000020000200011b0011000020001100002000020000200011000020000200002000110000200011000020000200011000020000200002000020001100002000020000200002000020000200002b00110000200002000110001100002000110000200011000020001100002,
  0x20018200011030020019100182000020300200182000020000200002000110018200002600020000200182000110300200182001820000203011b0011001820001103002000020000200011600020000200182000110300200191001820000203011001820000200002000020001100182000026000200182000020000200002b01910018200002030110019100182000110000200011001820001100002,
  0x38011000003801100000000000000000000000003800000000380110000000000000000000000000380110000038000000000000000011b0011000003801100000380000000000011000000000000000380110000038011000000000000011000000000038000000003801100000000000000000000000003800000000b00110000000000000113801100000380110000038011000000001100000,
  0x20018200011030020019100182000020300200182000020000200002000110018200002600020000200182000110300200182001820000203011b0011001820001103002000020000200011600020000200182000110300200191001820000203011001820000200002000020001100182000026000200182000020000200002b01910018200002030110019100182000110000200011001820001100002
]

/-! ### States, the step and the check -/

/-- The block `00111`, letter `p` at phase `p`. -/
def w00111 : List Bool := [false, false, true, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `5 w .. 5 w + 4` of table
`8 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (8 * p + s) 0 >>> (5 * w)) % 32

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `11`, `1001`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 3) ||
    ((2 * s + b.toNat) % 16 == 9)

/-- The last 3 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 8 else s

/-- The window of columns 1..8 after a step from phase `p`, with column 9 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 8 (w00111.getD p false) z w

/-- The certificate at one state: ranks are at most 22; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 5) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 5) (sNext p s w) (wNext p w true)
  decide (r ≤ 22) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 256

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 8 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 8 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 8 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 8 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 8 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 5 → allBelowT (partOK p) 8 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | p + 5, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 5) (hs : s < 8) (hw : w < 2 ^ 8) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 8 = 256 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 22 ∧
      (rk p s w = 0 → rk ((p + 1) % 5) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 5) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `00111` read from phase `ph`: letter `(t + ph) % 5` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w00111.getD ((t + ph) % 5) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..8` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 8
  | t + 1 => stripStep 8 (F t 0) (F t 9) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 8 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 8).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last three readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 5) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 8
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 8
    unfold sNext
    cases ((t + ph) % 5 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 8

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 5) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 9) := by
  show stripStep 8 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `22 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 22 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 9)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 5 = ((t + ph) % 5 + 1) % 5 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 22 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 22 ≤ t) (hp : (t + ph) % 5 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 5 = 0) :
    suf ph (drv (ctr ph) R) (t + 5) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 5) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  rw [h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_11 : ∀ s, s < 8 → badB (push s true) true = true := by decide
theorem bad_1001 : ∀ s, s < 8 → badB (push (push (push s true) false) false) true = true := by decide

end ReadingWords.B00111

open ReadingWords.B00111

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `11`.** At the first white steps, column 1 never reads `11` with the first reading at time `17` or
later. -/
theorem no_11_time_00111 (u : Nat) (hu : 17 ≤ u) (hp : (u + ph) % 5 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 5) 1 = true) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 5) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_11 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `1001`.** At the first white steps, column 1 never reads `1001` with the first reading at time `7` or
later. -/
theorem no_1001_time_00111 (u : Nat) (hu : 7 ≤ u) (hp : (u + ph) % 5 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 5) 1 = false ∧ drv (ctr ph) R (u + 10) 1 = false ∧
      drv (ctr ph) R (u + 15) 1 = true) := by
  rintro ⟨h0, h1, h2, h3⟩
  rw [show u + 10 = u + 5 + 5 by omega] at h2
  rw [show u + 15 = u + 5 + 5 + 5 by omega] at h3
  have hb := no_bad R ph (u + 5 + 5 + 5) (by omega) (by omega)
  rw [suf_period R ph (u + 5 + 5) (by omega), suf_period R ph (u + 5) (by omega), suf_period R ph u hp, h0, h1, h2,
    h3] at hb
  rw [bad_1001 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B00111

/-- A sequence of bits has none of the factors `11`, `1001` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = false ∧ b (i + 3) = true)

/-- Column 1 of the right half driven by `00111` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 5 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (5 * i + (5 - ph % 5) % 5) 1

end ReadingWords.B00111

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`11`, `1001` from the 4th on. -/
theorem readings_00111 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 4 := by
  intro i hi
  have hp : (5 * i + (5 - ph % 5) % 5 + ph) % 5 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 5) 1 := by
    unfold reading; rw [show 5 * (i + 1) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 5 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 10) 1 := by
    unfold reading; rw [show 5 * (i + 2) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 10 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (5 * i + (5 - ph % 5) % 5 + 15) 1 := by
    unfold reading; rw [show 5 * (i + 3) + (5 - ph % 5) % 5 = 5 * i + (5 - ph % 5) % 5 + 15 by omega]
  rw [e1, e2, e3]
  exact ⟨no_11_time_00111 R ph _ (by omega) hp, no_1001_time_00111 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `00111` -/

namespace ReadingWords.B00111

/-- From time `T` on, a row whose center column repeats `00111` from `T` has the right half driven by `00111` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w00111.getD ((t - T) % 5) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w00111.getD ((0 + 0) % 5) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w00111.getD ((t + 1 + 0) % 5) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B00111

/-- **Readings of every row.** If the center column of a row repeats `00111` from time `T` (letter
`(t - T) % 5` at time `t`), then column 1 at the times `T + 5 i` avoids `11`, `1001` from `i = 4` on. -/
theorem readings_00111_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w00111.getD ((t - T) % 5) false) :
    Avoids (fun i => evolve init (T + 5 * i) 1) 4 := by
  have e : (fun i => evolve init (T + 5 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 5 * i = T + (5 * i + (5 - 0 % 5) % 5) by omega]
    exact evolve_eq_drv init T h (5 * i + (5 - 0 % 5) % 5) 1
  rw [e]
  exact readings_00111 _ 0

end B00111

/-! ## Block `01011` -/

section B01011

/-! The certificate and the helpers live in `ReadingWords.B01011`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B01011

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `2 * p + s` packs the rank of window `w` in bits `3 w .. 3 w + 2`. -/
def rankTabs : List Nat := [
  0x0,
  0x3,
  0x0,
  0x2,
  0x0,
  0x208,
  0x0,
  0x5,
  0x0,
  0x820
]

/-! ### States, the step and the check -/

/-- The block `01011`, letter `p` at phase `p`. -/
def w01011 : List Bool := [false, true, false, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `3 w .. 3 w + 2` of table
`2 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (2 * p + s) 0 >>> (3 * w)) % 8

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `11`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 3)

/-- The last 1 readings after a step from phase `p` with window `w`: at phase 2 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 2 then (2 * s + (w.testBit 0).toNat) % 2 else s

/-- The window of columns 1..2 after a step from phase `p`, with column 3 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 2 (w01011.getD p false) z w

/-- The certificate at one state: ranks are at most 5; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 5) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 5) (sNext p s w) (wNext p w true)
  decide (r ≤ 5) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 2 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 4

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 2 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 2 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 2 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 2 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 2 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 5 → allBelowT (partOK p) 2 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | p + 5, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 5) (hs : s < 2) (hw : w < 2 ^ 2) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 2 = 4 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 5 ∧
      (rk p s w = 0 → rk ((p + 1) % 5) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 2 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 5) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `01011` read from phase `ph`: letter `(t + ph) % 5` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w01011.getD ((t + ph) % 5) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..2` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 2
  | t + 1 => stripStep 2 (F t 0) (F t 3) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 2 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 2).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last one readings of column 1 at the second white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 5) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 2
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 2
    unfold sNext
    cases ((t + ph) % 5 == 2)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 2) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 2

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 5) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 3) := by
  show stripStep 2 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `5 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 5 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 3)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 5 = ((t + ph) % 5 + 1) % 5 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 5) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 5 on, no reading at the second white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 5 ≤ t) (hp : (t + ph) % 5 = 2) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each second white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 5 = 2) :
    suf ph (drv (ctr ph) R) (t + 5) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 5) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 5) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  rw [h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_11 : ∀ s, s < 2 → badB (push s true) true = true := by decide

end ReadingWords.B01011

open ReadingWords.B01011

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `11`.** At the second white steps, column 1 never reads `11` with the first reading at time `0` or
later. -/
theorem no_11_time_01011 (u : Nat) (hu : 0 ≤ u) (hp : (u + ph) % 5 = 2) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 5) 1 = true) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 5) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_11 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B01011

/-- A sequence of bits has none of the factors `11` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true)

/-- Column 1 of the right half driven by `01011` from phase `ph`, at the `i`-th second white step (the steps `t` with
`(t + ph) % 5 = 2`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (5 * i + (2 + 5 - ph % 5) % 5) 1

end ReadingWords.B01011

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the second white steps avoid
`11` from the 0th on. -/
theorem readings_01011 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 0 := by
  intro i hi
  have hp : (5 * i + (2 + 5 - ph % 5) % 5 + ph) % 5 = 2 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (5 * i + (2 + 5 - ph % 5) % 5 + 5) 1 := by
    unfold reading; rw [show 5 * (i + 1) + (2 + 5 - ph % 5) % 5 = 5 * i + (2 + 5 - ph % 5) % 5 + 5 by omega]
  rw [e1]
  exact no_11_time_01011 R ph _ (by omega) hp

/-! ### Every row whose center column repeats `01011` -/

namespace ReadingWords.B01011

/-- From time `T` on, a row whose center column repeats `01011` from `T` has the right half driven by `01011` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w01011.getD ((t - T) % 5) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w01011.getD ((0 + 0) % 5) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w01011.getD ((t + 1 + 0) % 5) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B01011

/-- **Readings of every row.** If the center column of a row repeats `01011` from time `T` (letter
`(t - T) % 5` at time `t`), then column 1 at the times `T + 5 i + 2` avoids `11` from `i = 0` on. -/
theorem readings_01011_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w01011.getD ((t - T) % 5) false) :
    Avoids (fun i => evolve init (T + 5 * i + 2) 1) 0 := by
  have e : (fun i => evolve init (T + 5 * i + 2) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 5 * i + 2 = T + (5 * i + (2 + 5 - 0 % 5) % 5) by omega]
    exact evolve_eq_drv init T h (5 * i + (2 + 5 - 0 % 5) % 5) 1
  rw [e]
  exact readings_01011 _ 0

end B01011

/-! ## Block `000001` -/

section B000001

/-! The certificate and the helpers live in `ReadingWords.B000001`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B000001

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `4 * p + s` packs the rank of window `w` in bits `4 w .. 4 w + 3`. -/
def rankTabs : List Nat := [
  0xd000000000000000000000000000000000000000000000000000000000000000d000000000000000000000000000000000000000000000000000000000,
  0x101010d010101010101010101010101010101010101010101010101010101010101010d010101010101010101010101010101010101010101010101010101017,
  0x101010d010101010101010101010101010101010101010101010101010101010101010d010101010101010101010101010101010101010101010101010101010,
  0x101010d010101010101010101010101010101010101010101010101010101010101010d010101010101010101010101010101010101010101010101010101017,
  0x0,
  0xc0000000000c00000000000000000000c0000000000000000000000600000000c0000000000c000000000000000c0000c0000000c000000000000006,
  0x60000000000000000000000000000000000000000000000000000000000000006,
  0xc0000000000c00000000000000000000c0000000000000000000000600000000c0000000000c000000000000000c0000c0000000c000000000000006,
  0x0,
  0xb00000500000000000000b0000000000000000500000000000000b0000000000b00000500000000000000b000000b0000000b05,
  0x5000000000000000000000000000000050000000000000000000000000000000500000000000000000000000000000005,
  0xb00000500000000000000b0000000000000000500000000000000b0000000000b00000500000000000000b000000b0000000b05,
  0x0,
  0x400000000000000040000a0000000000400000000000000040000a000000000040000000000000004000000000000000400000000a0000004,
  0x40000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004,
  0x400000000000000040000a0000000000400000000000000040000a000000000040000000000000004000000000000000400000000a0000004,
  0x0,
  0x3000000030000000300000003000000030000000300000093000000030000000300000003000000030000000300000003000009030000000300000003,
  0x3000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003,
  0x3000000030000000300000003000000030000000300000093000000030000000300000003000000030000000300000003000009030000000300000003,
  0xe0000000000000000,
  0x800200020002000200020002000200020002000200020002000200020002000280020002000200020002000200020002000200020002000e0002000200020002,
  0x200020002000200020002000200020002000200020002000200020002000200020002000200020002000200020002000200020002000e0002000200020002,
  0x800200020002000200020002000200020002000200020002000200020002000280020002000200020002000200020002000200020002000e0002000200020002
]

/-! ### States, the step and the check -/

/-- The block `000001`, letter `p` at phase `p`. -/
def w000001 : List Bool := [false, false, false, false, false, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `4 w .. 4 w + 3` of table
`4 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (4 * p + s) 0 >>> (4 * w)) % 16

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `11`, `101`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 3) ||
    ((2 * s + b.toNat) % 8 == 5)

/-- The last 2 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 4 else s

/-- The window of columns 1..7 after a step from phase `p`, with column 8 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 7 (w000001.getD p false) z w

/-- The certificate at one state: ranks are at most 14; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 6) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 6) (sNext p s w) (wNext p w true)
  decide (r ≤ 14) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 128

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 4 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 4 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 4 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 4 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 4 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 4 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 6 → allBelowT (partOK p) 4 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | p + 6, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 6) (hs : s < 4) (hw : w < 2 ^ 7) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 7 = 128 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 14 ∧
      (rk p s w = 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `000001` read from phase `ph`: letter `(t + ph) % 6` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w000001.getD ((t + ph) % 6) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..7` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 7
  | t + 1 => stripStep 7 (F t 0) (F t 8) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 7 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 7).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last two readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 6) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 4
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 4
    unfold sNext
    cases ((t + ph) % 6 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 4

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 6) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 8) := by
  show stripStep 7 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `14 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 14 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 8)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 6 = ((t + ph) % 6 + 1) % 6 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 14 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 14 ≤ t) (hp : (t + ph) % 6 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 6 = 0) :
    suf ph (drv (ctr ph) R) (t + 6) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 6) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  rw [h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_11 : ∀ s, s < 4 → badB (push s true) true = true := by decide
theorem bad_101 : ∀ s, s < 4 → badB (push (push s true) false) true = true := by decide

end ReadingWords.B000001

open ReadingWords.B000001

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `11`.** At the first white steps, column 1 never reads `11` with the first reading at time `8` or
later. -/
theorem no_11_time_000001 (u : Nat) (hu : 8 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = true) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 6) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_11 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `101`.** At the first white steps, column 1 never reads `101` with the first reading at time `2` or
later. -/
theorem no_101_time_000001 (u : Nat) (hu : 2 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = false ∧ drv (ctr ph) R (u + 12) 1 = true) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 12 = u + 6 + 6 by omega] at h2
  have hb := no_bad R ph (u + 6 + 6) (by omega) (by omega)
  rw [suf_period R ph (u + 6) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_101 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B000001

/-- A sequence of bits has none of the factors `11`, `101` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = true)

/-- Column 1 of the right half driven by `000001` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 6 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (6 * i + (6 - ph % 6) % 6) 1

end ReadingWords.B000001

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`11`, `101` from the 2th on. -/
theorem readings_000001 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 2 := by
  intro i hi
  have hp : (6 * i + (6 - ph % 6) % 6 + ph) % 6 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 6) 1 := by
    unfold reading; rw [show 6 * (i + 1) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 6 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 12) 1 := by
    unfold reading; rw [show 6 * (i + 2) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 12 by omega]
  rw [e1, e2]
  exact ⟨no_11_time_000001 R ph _ (by omega) hp, no_101_time_000001 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `000001` -/

namespace ReadingWords.B000001

/-- From time `T` on, a row whose center column repeats `000001` from `T` has the right half driven by `000001` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w000001.getD ((t - T) % 6) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w000001.getD ((0 + 0) % 6) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w000001.getD ((t + 1 + 0) % 6) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B000001

/-- **Readings of every row.** If the center column of a row repeats `000001` from time `T` (letter
`(t - T) % 6` at time `t`), then column 1 at the times `T + 6 i` avoids `11`, `101` from `i = 2` on. -/
theorem readings_000001_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w000001.getD ((t - T) % 6) false) :
    Avoids (fun i => evolve init (T + 6 * i) 1) 2 := by
  have e : (fun i => evolve init (T + 6 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 6 * i = T + (6 * i + (6 - 0 % 6) % 6) by omega]
    exact evolve_eq_drv init T h (6 * i + (6 - 0 % 6) % 6) 1
  rw [e]
  exact readings_000001 _ 0

end B000001

/-! ## Block `000011` -/

section B000011

/-! The certificate and the helpers live in `ReadingWords.B000011`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B000011

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `32 * p + s` packs the rank of window `w` in bits `5 w .. 5 w + 4`. -/
def rankTabs : List Nat := [
  0xd000e000000000e00000d0000000000000000000d000e000000000e0000000000000000000000000d000e000000000e00000d0000000000000000000d0000000000003e000000000000000000000,
  0x640d004190641906419004190040100419004010040d004010640100419004010040100401004010640d00419064190641900419004010041900401004190040106401067f906419004010041900401,
  0x9826d980e000260980e00026d0000000260982609826d980e000000000e0002600026000260982609826d980e000260980e00026d0000000260982600026d0000000260983e000260002609826098260,
  0x640d000190641906419000190000000019000000000d000000640000019000000000000000000000640d00019064190641900019000000001900000000190000006400067f906419000000001900000,
  0xd000e000000000e00000d0000000000000000000d000e000000000e0000000000000000000000000d000e000000000e00000d0000000000000000000d0000000000003e000000000000000000000,
  0x640d004196e41906419004190040100419004010040d004010640100419684010040100401004010640d004196e419064190041900401004190040100419004016e401067f96e419004010041900401,
  0x9826d980e000260980e00026d0000000260982609826d980e000000000e0002600026000260982609826d980e000260980e00026d0000000260982600026d0000000260983e000260002609826098260,
  0x640d000190641906419000190000000019000000000d000000640000019000000000000000000000640d00019064190641900019000000001900000000190000006400067f906419000000001900000,
  0xd000e000000000e00000d0000000000000000000d000e000000000e0000000000000000000000000d000e000000000e00000d0000000000000000000d0000000000003e000000000000000000000,
  0x640d004190641906419004190040100419004010040d004010640100419004010040100401004010640d00419064190641900419004010041900401004190040106401067f906419004010041900401,
  0x9826d980e000260980e00026d0000000260982609826d980e000000000e0002600026000260982609826d980e000260980e00026d0000000260982600026d0000000260983e000260002609826098260,
  0x640d000f906419064f9000190000000019000000000d000e006400000f9000000000000000000000640d000f906419064f900019000000001900000000190000006400067f906419000000001900000,
  0xd000e000000000e00000d0000000000000000000d000e000000000e0000000000000000000000000d000e000000000e00000d0000000000000000000d0000000000003e000000000000000000000,
  0x640d004196e41906419004190040100419004010040d004010640100419684010040100401004010640d004196e419064190041900401004190040100419004016e401067f96e419004010041900401,
  0x9826d980e000260980e00026d0000000260982609826d980e000000000e0002600026000260982609826d980e000260980e00026d0000000260982600026d0000000260983e000260002609826098260,
  0x640d000190641906419000190000000019000000000d000000640000019000000000000000000000640d00019064190641900019000000001900000000190000006400067f906419000000001900000,
  0xd000e000000000e00000d0000000000000000000d000e000000000e0000000000000000000000000d000e000000000e00000d0000000000000000000d0000000000003e000000000000000000000,
  0x640d004190641906419004190040100419004010040d004010640100419004010040100401004010640d00419064190641900419004010041900401004190040106401067f906419004010041900401,
  0x9826d980e000260980e00026d0000000260982609826d980e000000000e0002600026000260982609826d980e000260980e00026d0000000260982600026d0000000260983e000260002609826098260,
  0x640d000190641906419000190000000019000000000d000000640000019000000000000000000000640d00019064190641900019000000001900000000190000006400067f906419000000001900000,
  0xd000e000000000e00000d0000000000000000000d000e000000000e0000000000000000000000000d000e000000000e00000d0000000000000000000d0000000000003e000000000000000000000,
  0x640d004196e41906419004190040100419004010040d004010640100419684010040100401004010640d004196e419064190041900401004190040100419004016e401067f96e419004010041900401,
  0x9826d980e000260980e00026d0000000260982609826d980e000000000e0002600026000260982609826d980e000260980e00026d0000000260982600026d0000000260983e000260002609826098260,
  0x640d004190641906419004190040100419004010040d004010640100419004010040100401004010640d00419064190641900419004010041900401004190040106401067f906419004010041900401,
  0xd000e000000000e00000d0000000000000000000d000e000000000e0000000000000000000000000d000e000000000e00000d0000000000000000000d0000000000003e000000000000000000000,
  0x640d004190641906419004190040100419004010040d004010640100419004010040100401004010640d00419064190641900419004010041900401004190040106401067f906419004010041900401,
  0x9826d980e000260980e00026d0000000260982609826d980e000000000e0002600026000260982609826d980e000260980e00026d0000000260982600026d0000000260983e000260002609826098260,
  0x640d000f906419064f9000190000000019000000000d000e006400000f9000000000000000000000640d000f906419064f900019000000001900000000190000006400067f906419000000001900000,
  0xd000e000000000e00000d0000000000000000000d000e000000000e0000000000000000000000000d000e000000000e00000d0000000000000000000d0000000000003e000000000000000000000,
  0x640d004196e41906419004190040100419004010040d004010640100419684010040100401004010640d004196e419064190041900401004190040100419004016e401067f96e419004010041900401,
  0x9826d980e000260980e00026d0000000260982609826d980e000000000e0002600026000260982609826d980e000260980e00026d0000000260982600026d0000000260983e000260002609826098260,
  0x640d000190641906419000190000000019000000000d000000640000019000000000000000000000640d00019064190641900019000000001900000000190000006400067f906419000000001900000,
  0x3000000000018000000030000300000000000000300000000000000000003000030000300000000030000000000180000000300003000000000000003000000000018000000030000300003000,
  0x1ef000030000000060000630000300000001e0000630000300000001e3000030000300000001e0001ef0000300000001e0000630000300000001e0000630000300000001e3000030000f00000001e,
  0xc6000033000001800180c0000030180631806300003000331800000c030006000063180300003000c63000331800018c0300c0000030180631806300c00000301806000c6300000180601803018c6300,
  0x1ef000000000000000000000000000000001e0000000000000000001e0000000000000000001e0001ef0000000000001e0000000000000000001e0000000000000000001e0000000000f00000001e,
  0x3000000000018000000030000300000000000000300000000000000000003000030000300000000030000000000180000000300003000000000000003000000000018000000030000300003000,
  0x94a5ef000034a409000604a4630000302529001e9480630000300000481e3025230240302529025e94a5ef000034a409481e04a4630000302529001e04a4630000302529481e34a4030240f02529025e,
  0xc6000033000001800180c0000030180631806300003000331800000c030006000063180300003000c63000331800018c0300c0000030180631806300c00000301806000c6300000180601803018c6300,
  0x1ef000000000000000000000000000000001e0000000000000000001e0000000000000000001e0001ef0000000000001e0000000000000000001e0000000000000000001e0000000000f00000001e,
  0x3000000000018000000030000300000000000000300000000000000000003000030000300000000030000000000180000000300003000000000000003000000000018000000030000300003000,
  0x1ef000030000000060000630000300000001e0000630000300000001e3000030000300000001e0001ef0000300000001e0000630000300000001e0000630000300000001e3000030000f00000001e,
  0xc6000033000001800180c0000030180631806300003000331800000c030006000063180300003000c63000331800018c0300c0000030180631806300c00000301806000c6300000180601803018c6300,
  0x1ef300000000001800000003000030000001e0000003000000000001e0000003000030000301e0001ef3000000000019e0000003000030000001e0000003000000000019e0000003000f30000301e,
  0x3000000000018000000030000300000000000000300000000000000000003000030000300000000030000000000180000000300003000000000000003000000000018000000030000300003000,
  0x94a5ef000034a409000604a4630000302529001e9480630000300000481e3025230240302529025e94a5ef000034a409481e04a4630000302529001e04a4630000302529481e34a4030240f02529025e,
  0xc6000033000001800180c0000030180631806300003000331800000c030006000063180300003000c63000331800018c0300c0000030180631806300c00000301806000c6300000180601803018c6300,
  0x1ef000000000000000000000000000000001e0000000000000000001e0000000000000000001e0001ef0000000000001e0000000000000000001e0000000000000000001e0000000000f00000001e,
  0x3000000000018000000030000300000000000000300000000000000000003000030000300000000030000000000180000000300003000000000000003000000000018000000030000300003000,
  0x1ef000030000000060000630000300000001e0000630000300000001e3000030000300000001e0001ef0000300000001e0000630000300000001e0000630000300000001e3000030000f00000001e,
  0xc6000033000001800180c0000030180631806300003000331800000c030006000063180300003000c63000331800018c0300c0000030180631806300c00000301806000c6300000180601803018c6300,
  0x1ef000000000000000000000000000000001e0000000000000000001e0000000000000000001e0001ef0000000000001e0000000000000000001e0000000000000000001e0000000000f00000001e,
  0x3000000000018000000030000300000000000000300000000000000000003000030000300000000030000000000180000000300003000000000000003000000000018000000030000300003000,
  0x94a5ef000034a409000604a4630000302529001e9480630000300000481e3025230240302529025e94a5ef000034a409481e04a4630000302529001e04a4630000302529481e34a4030240f02529025e,
  0xc6000033000001800180c0000030180631806300003000331800000c030006000063180300003000c63000331800018c0300c0000030180631806300c00000301806000c6300000180601803018c6300,
  0x1ef000030000000060000630000300000001e0000630000300000001e3000030000300000001e0001ef0000300000001e0000630000300000001e0000630000300000001e3000030000f00000001e,
  0x3000000000018000000030000300000000000000300000000000000000003000030000300000000030000000000180000000300003000000000000003000000000018000000030000300003000,
  0x1ef000030000000060000630000300000001e0000630000300000001e3000030000300000001e0001ef0000300000001e0000630000300000001e0000630000300000001e3000030000f00000001e,
  0xc6000033000001800180c0000030180631806300003000331800000c030006000063180300003000c63000331800018c0300c0000030180631806300c00000301806000c6300000180601803018c6300,
  0x1ef300000000001800000003000030000001e0000003000000000001e0000003000030000301e0001ef3000000000019e0000003000030000001e0000003000000000019e0000003000f30000301e,
  0x3000000000018000000030000300000000000000300000000000000000003000030000300000000030000000000180000000300003000000000000003000000000018000000030000300003000,
  0x94a5ef000034a409000604a4630000302529001e9480630000300000481e3025230240302529025e94a5ef000034a409481e04a4630000302529001e04a4630000302529481e34a4030240f02529025e,
  0xc6000033000001800180c0000030180631806300003000331800000c030006000063180300003000c63000331800018c0300c0000030180631806300c00000301806000c6300000180601803018c6300,
  0x1ef000000000000000000000000000000001e0000000000000000001e0000000000000000001e0001ef0000000000001e0000000000000000001e0000000000000000001e0000000000f00000001e,
  0x58000000000000000000580005800000000000000000000000000000000058000580000000000000580000000000000000005800058000000000000058000000000000000000580005800000000,
  0x74a500000014bd00000014a5014000141d00000074bd00000074bd00000014a5014000740500000074bd00000074bd00000014a5014000141d00000014a500000074bd00000017a5074000141d,
  0xb8017b8000b8000b8000000175800058017002e005ef7b8000b800000000bdc1758000582e000000bdef7b8000b8000b8000000175800058017002e00001758000bdc1700000b800058000b8017b82e0,
  0x7400000000001d0000000000000000001d000000741d000000741d00000000000000007400000000741d000000741d0000000000000000001d0000000000000000741d00000003a0074000001d,
  0x58000000000000000000580005800000000000000000000000000000000058000580000000000000580000000000000000005800058000000000000058000000000000000000580005800000000,
  0x8c620074a504620014bd04620014a5016318941d88000074bd00000074bd00220014a5014118f6258c620074bd04620074bd04620014a5016318941d04620014a5002208f4bd04620017a5076208963d,
  0xb8017b8000b8000b8000000175800058017002e005ef7b8000b800000000bdc1758000582e000000bdef7b8000b8000b8000000175800058017002e00001758000bdc1700000b800058000b8017b82e0,
  0x7400000000001d0000000000000000001d000000741d000000741d00000000000000007400000000741d000000741d0000000000000000001d0000000000000000741d00000003a0074000001d,
  0x58000000000000000000580005800000000000000000000000000000000058000580000000000000580000000000000000005800058000000000000058000000000000000000580005800000000,
  0x74a500000014bd00000014a5014000141d00000074bd00000074bd00000014a5014000740500000074bd00000074bd00000014a5014000141d00000014a500000074bd00000017a5074000141d,
  0xb8017b8000b8000b8000000175800058017002e005ef7b8000b800000000bdc1758000582e000000bdef7b8000b8000b8000000175800058017002e00001758000bdc1700000b800058000b8017b82e0,
  0x5f400000000001d0000058000580000001d000000741d000000741d00000580005800007400000005f41d000000741d0000058000580000001d0000058000000000741d00000583a05f4000001d,
  0x58000000000000000000580005800000000000000000000000000000000058000580000000000000580000000000000000005800058000000000000058000000000000000000580005800000000,
  0x8c620074a504620014bd04620014a5016318941d88000074bd00000074bd00220014a5014118f6258c620074bd04620074bd04620014a5016318941d04620014a5002208f4bd04620017a5076208963d,
  0xb8017b8000b8000b8000000175800058017002e005ef7b8000b800000000bdc1758000582e000000bdef7b8000b8000b8000000175800058017002e00001758000bdc1700000b800058000b8017b82e0,
  0x7400000000001d0000000000000000001d000000741d000000741d00000000000000007400000000741d000000741d0000000000000000001d0000000000000000741d00000003a0074000001d,
  0x58000000000000000000580005800000000000000000000000000000000058000580000000000000580000000000000000005800058000000000000058000000000000000000580005800000000,
  0x74a500000014bd00000014a5014000141d00000074bd00000074bd00000014a5014000740500000074bd00000074bd00000014a5014000141d00000014a500000074bd00000017a5074000141d,
  0xb8017b8000b8000b8000000175800058017002e005ef7b8000b800000000bdc1758000582e000000bdef7b8000b8000b8000000175800058017002e00001758000bdc1700000b800058000b8017b82e0,
  0x7400000000001d0000000000000000001d000000741d000000741d00000000000000007400000000741d000000741d0000000000000000001d0000000000000000741d00000003a0074000001d,
  0x58000000000000000000580005800000000000000000000000000000000058000580000000000000580000000000000000005800058000000000000058000000000000000000580005800000000,
  0x8c620074a504620014bd04620014a5016318941d88000074bd00000074bd00220014a5014118f6258c620074bd04620074bd04620014a5016318941d04620014a5002208f4bd04620017a5076208963d,
  0xb8017b8000b8000b8000000175800058017002e005ef7b8000b800000000bdc1758000582e000000bdef7b8000b8000b8000000175800058017002e00001758000bdc1700000b800058000b8017b82e0,
  0x74a500000014bd00000014a5014000141d00000074bd00000074bd00000014a5014000740500000074bd00000074bd00000014a5014000141d00000014a500000074bd00000017a5074000141d,
  0x58000000000000000000580005800000000000000000000000000000000058000580000000000000580000000000000000005800058000000000000058000000000000000000580005800000000,
  0x74a500000014bd00000014a5014000141d00000074bd00000074bd00000014a5014000740500000074bd00000074bd00000014a5014000141d00000014a500000074bd00000017a5074000141d,
  0xb8017b8000b8000b8000000175800058017002e005ef7b8000b800000000bdc1758000582e000000bdef7b8000b8000b8000000175800058017002e00001758000bdc1700000b800058000b8017b82e0,
  0x5f400000000001d0000058000580000001d000000741d000000741d00000580005800007400000005f41d000000741d0000058000580000001d0000058000000000741d00000583a05f4000001d,
  0x58000000000000000000580005800000000000000000000000000000000058000580000000000000580000000000000000005800058000000000000058000000000000000000580005800000000,
  0x8c620074a504620014bd04620014a5016318941d88000074bd00000074bd00220014a5014118f6258c620074bd04620074bd04620014a5016318941d04620014a5002208f4bd04620017a5076208963d,
  0xb8017b8000b8000b8000000175800058017002e005ef7b8000b800000000bdc1758000582e000000bdef7b8000b8000b8000000175800058017002e00001758000bdc1700000b800058000b8017b82e0,
  0x7400000000001d0000000000000000001d000000741d000000741d00000000000000007400000000741d000000741d0000000000000000001d0000000000000000741d00000003a0074000001d,
  0x140000000280000000001400000002800000000000000000000000000000000000000000000000001400000002800000000014000000028000000000140000000000000000001400000000000,
  0x200042001c200040001c200042001ce000400004e00042001c200040001c2001ce00042001c00004e00042001c200040001c200042001ce000400004200042001c2001c0001c20004e001c2001c0001c,
  0x594005800b2ac0002c005940058000280005800058000000005ac00000005ac005ac0b5800058000594005800b5ac0002c0059400580002800002c0059400000005ac00580005ac00580005ac0,
  0x1c000000001c000000001ce000000000e00000001c000000001c0001ce00000001c00000e00000001c000000001c000000001ce000000000000000001c0001c0001c00000e001c0001c0001c,
  0x140000000280000000001400000002800000000000000000000000000000000000000000000000001400000002800000000014000000028000000000140000000000000000001400000000000,
  0x242042001c202040001c240042001ce020480004e00042001c200040001c2021ce00042001c00204e42042001c202040001c240042001ce020480004240042001c2021c8001c20204e001c2021c8021c,
  0x594005800b2ac0002c005940058000280005800058000000005ac00000005ac005ac0b5800058000594005800b5ac0002c0059400580002800002c0059400000005ac00580005ac00580005ac0,
  0x1c000000001c000000001ce000000000e00000001c000000001c0001ce00000001c00000e00000001c000000001c000000001ce000000000000000001c0001c0001c00000e001c0001c0001c,
  0x140000000280000000001400000002800000000000000000000000000000000000000000000000001400000002800000000014000000028000000000140000000000000000001400000000000,
  0x200042001c200040001c200042001ce000400004e00042001c200040001c2001ce00042001c00004e00042001c200040001c200042001ce000400004200042001c2001c0001c20004e001c2001c0001c,
  0x594005800b2ac0002c005940058000280005800058000000005ac00000005ac005ac0b5800058000594005800b5ac0002c0059400580002800002c0059400000005ac00580005ac00580005ac0,
  0x15c000000281c000000015ce000002800e00000001c000000001c0001ce00000001c00000e00000015c000000281c000000015ce000002800000000015c0001c0001c00000e015c0001c0001c,
  0x140000000280000000001400000002800000000000000000000000000000000000000000000000001400000002800000000014000000028000000000140000000000000000001400000000000,
  0x242042001c202040001c240042001ce020480004e00042001c200040001c2021ce00042001c00204e42042001c202040001c240042001ce020480004240042001c2021c8001c20204e001c2021c8021c,
  0x594005800b2ac0002c005940058000280005800058000000005ac00000005ac005ac0b5800058000594005800b5ac0002c0059400580002800002c0059400000005ac00580005ac00580005ac0,
  0x1c000000001c000000001ce000000000e00000001c000000001c0001ce00000001c00000e00000001c000000001c000000001ce000000000000000001c0001c0001c00000e001c0001c0001c,
  0x140000000280000000001400000002800000000000000000000000000000000000000000000000001400000002800000000014000000028000000000140000000000000000001400000000000,
  0x200042001c200040001c200042001ce000400004e00042001c200040001c2001ce00042001c00004e00042001c200040001c200042001ce000400004200042001c2001c0001c20004e001c2001c0001c,
  0x594005800b2ac0002c005940058000280005800058000000005ac00000005ac005ac0b5800058000594005800b5ac0002c0059400580002800002c0059400000005ac00580005ac00580005ac0,
  0x1c000000001c000000001ce000000000e00000001c000000001c0001ce00000001c00000e00000001c000000001c000000001ce000000000000000001c0001c0001c00000e001c0001c0001c,
  0x140000000280000000001400000002800000000000000000000000000000000000000000000000001400000002800000000014000000028000000000140000000000000000001400000000000,
  0x242042001c202040001c240042001ce020480004e00042001c200040001c2021ce00042001c00204e42042001c202040001c240042001ce020480004240042001c2021c8001c20204e001c2021c8021c,
  0x594005800b2ac0002c005940058000280005800058000000005ac00000005ac005ac0b5800058000594005800b5ac0002c0059400580002800002c0059400000005ac00580005ac00580005ac0,
  0x200042001c200040001c200042001ce000400004e00042001c200040001c2001ce00042001c00004e00042001c200040001c200042001ce000400004200042001c2001c0001c20004e001c2001c0001c,
  0x140000000280000000001400000002800000000000000000000000000000000000000000000000001400000002800000000014000000028000000000140000000000000000001400000000000,
  0x200042001c200040001c200042001ce000400004e00042001c200040001c2001ce00042001c00004e00042001c200040001c200042001ce000400004200042001c2001c0001c20004e001c2001c0001c,
  0x594005800b2ac0002c005940058000280005800058000000005ac00000005ac005ac0b5800058000594005800b5ac0002c0059400580002800002c0059400000005ac00580005ac00580005ac0,
  0x15c000000281c000000015ce000002800e00000001c000000001c0001ce00000001c00000e00000015c000000281c000000015ce000002800000000015c0001c0001c00000e015c0001c0001c,
  0x140000000280000000001400000002800000000000000000000000000000000000000000000000001400000002800000000014000000028000000000140000000000000000001400000000000,
  0x242042001c202040001c240042001ce020480004e00042001c200040001c2021ce00042001c00204e42042001c202040001c240042001ce020480004240042001c2021c8001c20204e001c2021c8021c,
  0x594005800b2ac0002c005940058000280005800058000000005ac00000005ac005ac0b5800058000594005800b5ac0002c0059400580002800002c0059400000005ac00580005ac00580005ac0,
  0x1c000000001c000000001ce000000000e00000001c000000001c0001ce00000001c00000e00000001c000000001c000000001ce000000000000000001c0001c0001c00000e001c0001c0001c,
  0x480000000048000000000000000000000000000048000000000000000000000000000000000000004800000000480000000000000000004800000000480000000048000000000000000000,
  0xc0300f6306c1b00c6306c1b00c7b00c0306c6300c0300f7b00c1b00c6300c1b00c7b00c0300f7b00c0300f7b06c1b00c6306c1b00c7b00c0306c6306c1b00c7b00c1b00c7b06c1b00c7b00c1b00c63,
  0xa8000a80004800000000482a0a8000a82a000000a8000a8000480000000000000a8000a8000a8000a8000a80004800000000482a0a8000a82a000000482a0a800048000a800048000a8000a800000000,
  0x36006c1b0000006c1b0001b0000006c00000000037b0001b000000001b0001b000000037b000000037b06c1b0000006c1b0001b0000006c0006c1b0001b0001b0001b06c1b0001b0001b00000,
  0x480000000048000000000000000000000000000048000000000000000000000000000000000000004800000000480000000000000000004800000000480000000048000000000000000000,
  0xde300f6306dfb00c6306c1b00c7b00c037ec6300c0300f7b00c1b00c6300dfb00c7b00c0300f7b00de300f7b06dfb00c6306c1b00c7b00c037ec6306c1b00c7b00dfb00c7b06dfb00c7b00dfb78c63,
  0xa8000a80004800000000482a0a8000a82a000000a8000a8000480000000000000a8000a8000a8000a8000a80004800000000482a0a8000a82a000000482a0a800048000a800048000a8000a800000000,
  0x36006c1b0000006c1b0001b0000006c00000000037b0001b000000001b0001b000000037b000000037b06c1b0000006c1b0001b0000006c0006c1b0001b0001b0001b06c1b0001b0001b00000,
  0x480000000048000000000000000000000000000048000000000000000000000000000000000000004800000000480000000000000000004800000000480000000048000000000000000000,
  0xc0300f6306c1b00c6306c1b00c7b00c0306c6300c0300f7b00c1b00c6300c1b00c7b00c0300f7b00c0300f7b06c1b00c6306c1b00c7b00c0306c6306c1b00c7b00c1b00c7b06c1b00c7b00c1b00c63,
  0xa8000a80004800000000482a0a8000a82a000000a8000a8000480000000000000a8000a8000a8000a8000a80004800000000482a0a8000a82a000000482a0a800048000a800048000a8000a800000000,
  0x3604ec1b000004ec1b0001b0000006c00000000037b4801b000000001b0001b000000037b000000037b4ec1b000004ec1b0001b0000006c004ec1b0001b4801b0001b4ec1b0001b0001b00000,
  0x480000000048000000000000000000000000000048000000000000000000000000000000000000004800000000480000000000000000004800000000480000000048000000000000000000,
  0xde300f6306dfb00c6306c1b00c7b00c037ec6300c0300f7b00c1b00c6300dfb00c7b00c0300f7b00de300f7b06dfb00c6306c1b00c7b00c037ec6306c1b00c7b00dfb00c7b06dfb00c7b00dfb78c63,
  0xa8000a80004800000000482a0a8000a82a000000a8000a8000480000000000000a8000a8000a8000a8000a80004800000000482a0a8000a82a000000482a0a800048000a800048000a8000a800000000,
  0x36006c1b0000006c1b0001b0000006c00000000037b0001b000000001b0001b000000037b000000037b06c1b0000006c1b0001b0000006c0006c1b0001b0001b0001b06c1b0001b0001b00000,
  0x480000000048000000000000000000000000000048000000000000000000000000000000000000004800000000480000000000000000004800000000480000000048000000000000000000,
  0xc0300f6306c1b00c6306c1b00c7b00c0306c6300c0300f7b00c1b00c6300c1b00c7b00c0300f7b00c0300f7b06c1b00c6306c1b00c7b00c0306c6306c1b00c7b00c1b00c7b06c1b00c7b00c1b00c63,
  0xa8000a80004800000000482a0a8000a82a000000a8000a8000480000000000000a8000a8000a8000a8000a80004800000000482a0a8000a82a000000482a0a800048000a800048000a8000a800000000,
  0x36006c1b0000006c1b0001b0000006c00000000037b0001b000000001b0001b000000037b000000037b06c1b0000006c1b0001b0000006c0006c1b0001b0001b0001b06c1b0001b0001b00000,
  0x480000000048000000000000000000000000000048000000000000000000000000000000000000004800000000480000000000000000004800000000480000000048000000000000000000,
  0xde300f6306dfb00c6306c1b00c7b00c037ec6300c0300f7b00c1b00c6300dfb00c7b00c0300f7b00de300f7b06dfb00c6306c1b00c7b00c037ec6306c1b00c7b00dfb00c7b06dfb00c7b00dfb78c63,
  0xa8000a80004800000000482a0a8000a82a000000a8000a8000480000000000000a8000a8000a8000a8000a80004800000000482a0a8000a82a000000482a0a800048000a800048000a8000a800000000,
  0xc0300f6306c1b00c6306c1b00c7b00c0306c6300c0300f7b00c1b00c6300c1b00c7b00c0300f7b00c0300f7b06c1b00c6306c1b00c7b00c0306c6306c1b00c7b00c1b00c7b06c1b00c7b00c1b00c63,
  0x480000000048000000000000000000000000000048000000000000000000000000000000000000004800000000480000000000000000004800000000480000000048000000000000000000,
  0xc0300f6306c1b00c6306c1b00c7b00c0306c6300c0300f7b00c1b00c6300c1b00c7b00c0300f7b00c0300f7b06c1b00c6306c1b00c7b00c0306c6306c1b00c7b00c1b00c7b06c1b00c7b00c1b00c63,
  0xa8000a80004800000000482a0a8000a82a000000a8000a8000480000000000000a8000a8000a8000a8000a80004800000000482a0a8000a82a000000482a0a800048000a800048000a8000a800000000,
  0x3604ec1b000004ec1b0001b0000006c00000000037b4801b000000001b0001b000000037b000000037b4ec1b000004ec1b0001b0000006c004ec1b0001b4801b0001b4ec1b0001b0001b00000,
  0x480000000048000000000000000000000000000048000000000000000000000000000000000000004800000000480000000000000000004800000000480000000048000000000000000000,
  0xde300f6306dfb00c6306c1b00c7b00c037ec6300c0300f7b00c1b00c6300dfb00c7b00c0300f7b00de300f7b06dfb00c6306c1b00c7b00c037ec6306c1b00c7b00dfb00c7b06dfb00c7b00dfb78c63,
  0xa8000a80004800000000482a0a8000a82a000000a8000a8000480000000000000a8000a8000a8000a8000a80004800000000482a0a8000a82a000000482a0a800048000a800048000a8000a800000000,
  0x36006c1b0000006c1b0001b0000006c00000000037b0001b000000001b0001b000000037b000000037b06c1b0000006c1b0001b0000006c0006c1b0001b0001b0001b06c1b0001b0001b00000,
  0x700000000000000001c000008000000000000000700080000000000001c000000000000000000000700080000000000001c0000080000000000000007000800000000000000000000,
  0x10b4010b40d6840d084010b4010840d09c0d6b401084010840d084070840d6b40d0b4010b40d084010b4010b40d6840d084010b4010840d09c0d6b4010b4010840d6b4076840d68401084010b40d0840,
  0x140001400000700000000000014001d400008000000001400000700080000000014001c000014000140001400000700080000000014001d4000080000000014000007000800000000140000000014,
  0x34000340d6800d00000034000000d01c0d6b400000000000d000070000d6b40d034000340d00000034000340d6800d00000034000000d01c0d6b400034000000d6b4076800d68000000000340d0000,
  0x700000000000000001c000008000000000000000700080000000000001c000000000000000000000700080000000000001c0000080000000000000007000800000000000000000000,
  0x10b4010b40d684ed084010b4010840d09c0d6b401084010840d084070840d6b4ed0b4010b40d084010b4010b40d684ed084010b4010840d09c0d6b4010b4010840d6b4e76840d684e1084010b4ed0840,
  0x140001400000700000000000014001d400008000000001400000700080000000014001c000014000140001400000700080000000014001d4000080000000014000007000800000000140000000014,
  0x34000340d6800d00000034000000d01c0d6b400000000000d000070000d6b40d034000340d00000034000340d6800d00000034000000d01c0d6b400034000000d6b4076800d68000000000340d0000,
  0x700000000000000001c000008000000000000000700080000000000001c000000000000000000000700080000000000001c0000080000000000000007000800000000000000000000,
  0x10b4010b40d6840d084010b4010840d09c0d6b401084010840d084070840d6b40d0b4010b40d084010b4010b40d6840d084010b4010840d09c0d6b4010b4010840d6b4076840d68401084010b40d0840,
  0x140001400000700000000000014001d400008000000001400000700080000000014001c000014000140001400000700080000000014001d4000080000000014000007000800000000140000000014,
  0x34000340d6800d00000034000000d01c0d6b480000000000d000070008d6b40d034000340d00000034000340d6800d00080034000000d01c0d6b480034000000d6b4076808d68000000000340d0000,
  0x700000000000000001c000008000000000000000700080000000000001c000000000000000000000700080000000000001c0000080000000000000007000800000000000000000000,
  0x10b4010b40d684ed084010b4010840d09c0d6b401084010840d084070840d6b4ed0b4010b40d084010b4010b40d684ed084010b4010840d09c0d6b4010b4010840d6b4e76840d684e1084010b4ed0840,
  0x140001400000700000000000014001d400008000000001400000700080000000014001c000014000140001400000700080000000014001d4000080000000014000007000800000000140000000014,
  0x34000340d6800d00000034000000d01c0d6b400000000000d000070000d6b40d034000340d00000034000340d6800d00000034000000d01c0d6b400034000000d6b4076800d68000000000340d0000,
  0x700000000000000001c000008000000000000000700080000000000001c000000000000000000000700080000000000001c0000080000000000000007000800000000000000000000,
  0x10b4010b40d6840d084010b4010840d09c0d6b401084010840d084070840d6b40d0b4010b40d084010b4010b40d6840d084010b4010840d09c0d6b4010b4010840d6b4076840d68401084010b40d0840,
  0x140001400000700000000000014001d400008000000001400000700080000000014001c000014000140001400000700080000000014001d4000080000000014000007000800000000140000000014,
  0x34000340d6800d00000034000000d01c0d6b400000000000d000070000d6b40d034000340d00000034000340d6800d00000034000000d01c0d6b400034000000d6b4076800d68000000000340d0000,
  0x700000000000000001c000008000000000000000700080000000000001c000000000000000000000700080000000000001c0000080000000000000007000800000000000000000000,
  0x10b4010b40d684ed084010b4010840d09c0d6b401084010840d084070840d6b4ed0b4010b40d084010b4010b40d684ed084010b4010840d09c0d6b4010b4010840d6b4e76840d684e1084010b4ed0840,
  0x140001400000700000000000014001d400008000000001400000700080000000014001c000014000140001400000700080000000014001d4000080000000014000007000800000000140000000014,
  0x10b4010b40d6840d084010b4010840d09c0d6b401084010840d084070840d6b40d0b4010b40d084010b4010b40d6840d084010b4010840d09c0d6b4010b4010840d6b4076840d68401084010b40d0840,
  0x700000000000000001c000008000000000000000700080000000000001c000000000000000000000700080000000000001c0000080000000000000007000800000000000000000000,
  0x10b4010b40d6840d084010b4010840d09c0d6b401084010840d084070840d6b40d0b4010b40d084010b4010b40d6840d084010b4010840d09c0d6b4010b4010840d6b4076840d68401084010b40d0840,
  0x140001400000700000000000014001d400008000000001400000700080000000014001c000014000140001400000700080000000014001d4000080000000014000007000800000000140000000014,
  0x34000340d6800d00000034000000d01c0d6b480000000000d000070008d6b40d034000340d00000034000340d6800d00080034000000d01c0d6b480034000000d6b4076808d68000000000340d0000,
  0x700000000000000001c000008000000000000000700080000000000001c000000000000000000000700080000000000001c0000080000000000000007000800000000000000000000,
  0x10b4010b40d684ed084010b4010840d09c0d6b401084010840d084070840d6b4ed0b4010b40d084010b4010b40d684ed084010b4010840d09c0d6b4010b4010840d6b4e76840d684e1084010b4ed0840,
  0x140001400000700000000000014001d400008000000001400000700080000000014001c000014000140001400000700080000000014001d4000080000000014000007000800000000140000000014,
  0x34000340d6800d00000034000000d01c0d6b400000000000d000070000d6b40d034000340d00000034000340d6800d00000034000000d01c0d6b400034000000d6b4076800d68000000000340d0000
]

/-! ### States, the step and the check -/

/-- The block `000011`, letter `p` at phase `p`. -/
def w000011 : List Bool := [false, false, false, false, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `5 w .. 5 w + 4` of table
`32 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (32 * p + s) 0 >>> (5 * w)) % 32

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `010`, `101110`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 8 == 2) ||
    ((2 * s + b.toNat) % 64 == 46)

/-- The last 5 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 32 else s

/-- The window of columns 1..7 after a step from phase `p`, with column 8 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 7 (w000011.getD p false) z w

/-- The certificate at one state: ranks are at most 31; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 6) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 6) (sNext p s w) (wNext p w true)
  decide (r ≤ 31) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 128

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 32 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 32 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 32 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 32 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 32 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 32 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 6 → allBelowT (partOK p) 32 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | p + 6, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 6) (hs : s < 32) (hw : w < 2 ^ 7) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 7 = 128 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 31 ∧
      (rk p s w = 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `000011` read from phase `ph`: letter `(t + ph) % 6` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w000011.getD ((t + ph) % 6) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..7` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 7
  | t + 1 => stripStep 7 (F t 0) (F t 8) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 7 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 7).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last five readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 6) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 32
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 32
    unfold sNext
    cases ((t + ph) % 6 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 32

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 6) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 8) := by
  show stripStep 7 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `31 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 31 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 8)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 6 = ((t + ph) % 6 + 1) % 6 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 31 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 31 ≤ t) (hp : (t + ph) % 6 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 6 = 0) :
    suf ph (drv (ctr ph) R) (t + 6) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 6) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  rw [h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_010 : ∀ s, s < 32 → badB (push (push s false) true) false = true := by decide +kernel
theorem bad_101110 : ∀ s, s < 32 → badB (push (push (push (push (push s true) false) true) true) true) false = true
    := by decide +kernel

end ReadingWords.B000011

open ReadingWords.B000011

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `010`.** At the first white steps, column 1 never reads `010` with the first reading at time `19` or
later. -/
theorem no_010_time_000011 (u : Nat) (hu : 19 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = false ∧ drv (ctr ph) R (u + 6) 1 = true ∧ drv (ctr ph) R (u + 12) 1 = false) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 12 = u + 6 + 6 by omega] at h2
  have hb := no_bad R ph (u + 6 + 6) (by omega) (by omega)
  rw [suf_period R ph (u + 6) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_010 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `101110`.** At the first white steps, column 1 never reads `101110` with the first reading at time `1` or
later. -/
theorem no_101110_time_000011 (u : Nat) (hu : 1 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = false ∧ drv (ctr ph) R (u + 12) 1 = true ∧
      drv (ctr ph) R (u + 18) 1 = true ∧ drv (ctr ph) R (u + 24) 1 = true ∧ drv (ctr ph) R (u + 30) 1 = false) := by
  rintro ⟨h0, h1, h2, h3, h4, h5⟩
  rw [show u + 12 = u + 6 + 6 by omega] at h2
  rw [show u + 18 = u + 6 + 6 + 6 by omega] at h3
  rw [show u + 24 = u + 6 + 6 + 6 + 6 by omega] at h4
  rw [show u + 30 = u + 6 + 6 + 6 + 6 + 6 by omega] at h5
  have hb := no_bad R ph (u + 6 + 6 + 6 + 6 + 6) (by omega) (by omega)
  rw [suf_period R ph (u + 6 + 6 + 6 + 6) (by omega), suf_period R ph (u + 6 + 6 + 6) (by omega),
    suf_period R ph (u + 6 + 6) (by omega), suf_period R ph (u + 6) (by omega), suf_period R ph u hp, h0, h1, h2, h3,
    h4, h5] at hb
  rw [bad_101110 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B000011

/-- A sequence of bits has none of the factors `010`, `101110` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = false ∧ b (i + 1) = true ∧ b (i + 2) = false) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = true ∧ b (i + 3) = true ∧ b (i + 4) = true ∧ b (i + 5) = false)

/-- Column 1 of the right half driven by `000011` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 6 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (6 * i + (6 - ph % 6) % 6) 1

end ReadingWords.B000011

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`010`, `101110` from the 4th on. -/
theorem readings_000011 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 4 := by
  intro i hi
  have hp : (6 * i + (6 - ph % 6) % 6 + ph) % 6 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 6) 1 := by
    unfold reading; rw [show 6 * (i + 1) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 6 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 12) 1 := by
    unfold reading; rw [show 6 * (i + 2) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 12 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 18) 1 := by
    unfold reading; rw [show 6 * (i + 3) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 18 by omega]
  have e4 : reading R ph (i + 4) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 24) 1 := by
    unfold reading; rw [show 6 * (i + 4) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 24 by omega]
  have e5 : reading R ph (i + 5) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 30) 1 := by
    unfold reading; rw [show 6 * (i + 5) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 30 by omega]
  rw [e1, e2, e3, e4, e5]
  exact ⟨no_010_time_000011 R ph _ (by omega) hp, no_101110_time_000011 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `000011` -/

namespace ReadingWords.B000011

/-- From time `T` on, a row whose center column repeats `000011` from `T` has the right half driven by `000011` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w000011.getD ((t - T) % 6) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w000011.getD ((0 + 0) % 6) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w000011.getD ((t + 1 + 0) % 6) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B000011

/-- **Readings of every row.** If the center column of a row repeats `000011` from time `T` (letter
`(t - T) % 6` at time `t`), then column 1 at the times `T + 6 i` avoids `010`, `101110` from `i = 4` on. -/
theorem readings_000011_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w000011.getD ((t - T) % 6) false) :
    Avoids (fun i => evolve init (T + 6 * i) 1) 4 := by
  have e : (fun i => evolve init (T + 6 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 6 * i = T + (6 * i + (6 - 0 % 6) % 6) by omega]
    exact evolve_eq_drv init T h (6 * i + (6 - 0 % 6) % 6) 1
  rw [e]
  exact readings_000011 _ 0

end B000011

/-! ## Block `000111` -/

section B000111

/-! The certificate and the helpers live in `ReadingWords.B000111`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B000111

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `8 * p + s` packs the rank of window `w` in bits `5 w .. 5 w + 4`. -/
def rankTabs : List Nat := [
  0x2600000000000680000000000000000190000000000000000000000000001a00000000000000009826000000680006800000000000000000068000000000000000000000000000000000001a000000982600000068000680000000000000000190000000000000000000000000001a0000000000000000000000000000000680000000000000000006800000000000000000000000000009800000000,
  0x8020082600802d08020680200802008020080390b420080200802d080200802d081a00802008027080209826008020680206802008020080200802768020080200802d0b4200802d080200802d081a008020982600802d68020680200802008020080390b420080200802d080200802d081a008020080270b420080200802d080206802008020080200802768020080200802d0b4200802d080209802d08020,
  0x8020082600802008020680200802008020080390802008020080200802008020081a00802008027080209826008020680206802008020080200802768020080200802008020080200802008020081a008020982600802068020680200802008020080390802008020080200802008020081a0080200802708020080200802008020680200802008020080276802008020080200802008020080209802008020,
  0x8020082600802d08020680200802008020080390b420080200802d080200802d081a00802008027080209826008020680206802008020080200802768020080200802d0b4200802d080200802d081a008020982600802d68020680200802008020080390b420080200802d080200802d081a008020080270b420080200802d080206802008020080200802768020080200802d0b4200802d080209802d08020,
  0x8020082600802008020680200802008020080390802008020080200802008020081a00802008020080209826008020680206802008020080200802068020080200802008020080200802008020081a008020982600802068020680200802008020080390802008020080200802008020081a0080200802008020080200802008020680200802008020080206802008020080200802008020080209802008020,
  0x8020082600802d08020680200802008020080390b420080200802d080200802d081a00802008027080209826008020680206802008020080200802768020080200802d0b4200802d080200802d081a008020982600802d68020680200802008020080390b420080200802d080200802d081a008020080270b420080200802d080206802008020080200802768020080200802d0b4200802d080209802d08020,
  0x8020082600802008020680200802008020080390802008020080200802008020081a00802008027080209826008020680206802008020080200802768020080200802008020080200802008020081a008020982600802068020680200802008020080390802008020080200802008020081a0080200802708020080200802008020680200802008020080276802008020080200802008020080209802008020,
  0x8020082600802d08020680200802008020080390b420080200802d080200802d081a00802008027080209826008020680206802008020080200802768020080200802d0b4200802d080200802d081a008020982600802d68020680200802008020080390b420080200802d080200802d081a008020080270b420080200802d080206802008020080200802768020080200802d0b4200802d080209802d08020,
  0x1800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180000000000000000000000000000000000000018000000000000000000000000000000000000001800000000000000000000,
  0x6001200000930000000600000000000000c0018600000048009300004818030000000000000648006001200000000000000600000000000000c0018600192000000000000006930000024004800000006001200000930000000600000000000000c0018600000048009300004818030000000000000648000000004800930000481800192000000000c001860000000000930000481893000000000000000012,
  0x6000000000030000000600000000000000c0018600000000000300000018030000000000000600006000000000000000000600000000000000c0018600180000000000000006030000000000000000006000000000030000000600000000000000c0018600000000000300000018030000000000000600000000000000030000001800180000000000c001860000000000030000001803000000000000000000,
  0x6001200000930000000600000000000000c0018600000048009300004818030000000000000648006001200000000000000600000000000000c0018600192000000000000006930000024004800000006001200000930000000600000000000000c0018600000048009300004818030000000000000648000000004800930000481800192000000000c001860000000000930000481893000000000000000012,
  0x6000000000000000000060000000000000000001800000000000000000000000000000000000000060000000000000000000600000000000000000006000000000000000000000000000000000000000600000000000000000006000000000000000000180000000000000000000000000000000000000018000000000000000000060000000000000000001800000000000000000000,
  0x6001200000930000000600000000000000c0018600000048009300004818030000000000000648006001200000000000000600000000000000c0018600192000000000000006930000024004800000006001200000930000000600000000000000c0018600000048009300004818030000000000000648000000004800930000481800192000000000c001860000000000930000481893000000000000000012,
  0x6000000000030000000600000000000000c0018600000000000300000018030000000000000600006000000000000000000600000000000000c0018600180000000000000006030000000000000000006000000000030000000600000000000000c0018600000000000300000018030000000000000600000000000000030000001800180000000000c001860000000000030000001803000000000000000000,
  0x6001200000930000000600000000000000c0018600000048009300004818030000000000000648006001200000000000000600000000000000c0018600192000000000000006930000024004800000006001200000930000000600000000000000c0018600000048009300004818030000000000000648000000004800930000481800192000000000c001860000000000930000481893000000000000000012,
  0x17000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001700000000000000000000000000000000000000170000000000000000000000000000000000000000000000000000000000000000000000,
  0x50000000005000000000504560000008ac000441700000582250000088005000110440002c0004405000005800500000000058800000000000000000500000000050000004405044000017102c0004405000005800500000000058c560000008ac00044170000058225000008800500011044008ac00044170000058225000000000588000000000000000005000005822500000000050440004560,
  0x500000000050000000005001600000002c000001700000580050000000005000000000002c0000005000005800500000000050000000000000000000500000000050000000005000000016002c000000500000580050000000005001600000002c000001700000580050000000005000000000002c00000170000058005000000000500000000000000000005000005800500000000050000000160,
  0x50000000005000000000504560000008ac000441700000582250000088005000110440002c0004405000005800500000000058800000000000000000500000000050000004405044000017102c0004405000005800500000000058c560000008ac00044170000058225000008800500011044008ac00044170000058225000000000588000000000000000005000005822500000000050440004560,
  0x50000000005000000000500000000000000000017000000000500000000050000000000000000000500000000050000000005000000000000000000050000000005000000000500000000000000000005000000000500000000050000000000000000001700000000050000000005000000000000000000170000000005000000000500000000000000000005000000000500000000050000000000,
  0x50000000005000000000504560000008ac000441700000582250000088005000110440002c0004405000005800500000000058800000000000000000500000000050000004405044000017102c0004405000005800500000000058c560000008ac00044170000058225000008800500011044008ac00044170000058225000000000588000000000000000005000005822500000000050440004560,
  0x500000000050000000005001600000002c000001700000580050000000005000000000002c0000005000005800500000000050000000000000000000500000000050000000005000000016002c000000500000580050000000005001600000002c000001700000580050000000005000000000002c00000170000058005000000000500000000000000000005000005800500000000050000000160,
  0x50000000005000000000504560000008ac000441700000582250000088005000110440002c0004405000005800500000000058800000000000000000500000000050000004405044000017102c0004405000005800500000000058c560000008ac00044170000058225000008800500011044008ac00044170000058225000000000588000000000000000005000005822500000000050440004560,
  0x16000000000000000000000000000000000000000000000000000000000000000000001600000000000001000000000000000000000000000000000000000000000000000000000000000000000000001600000000000000000000000000000000000000000000000010000000000000000000160000000000000000001600000,
  0x4002040000400000040040000480004040000014480004000040000000016800040000450210000040020400004000000400400004800040000000144000040001600010000048001080004500000000400204000040000004004000048000404000001448000400004000000001680004000045021000144800040000400000041440000480010040000400400004000160000000004000040001600000,
  0x4000040000400000000040000400004000000014400004000040000000016000040000450000000040000400004000000000400004000040000000144000040001600000000040001000004500000000400004000040000000004000040000400000001440000400004000000001600004000045000000144000040000400000001440000400010000000000400004000160000000004000040001600000,
  0x4002040000400000040040000480004040000014480004000040000000016800040000450210000040020400004000000400400004800040000000144000040001600010000048001080004500000000400204000040000004004000048000404000001448000400004000000001680004000045021000144800040000400000041440000480010040000400400004000160000000004000040001600000,
  0x4000040000400000000040000400004000000000400004000040000000016000040000400000000040000400004000000000400004000040000000004000040001600000000040001000004000000000400004000040000000004000040000400000000040000400004000000001600004000040000000004000040000400000000040000400010000000000400004000160000000004000040001600000,
  0x4002040000400000040040000480004040000014480004000040000000016800040000450210000040020400004000000400400004800040000000144000040001600010000048001080004500000000400204000040000004004000048000404000001448000400004000000001680004000045021000144800040000400000041440000480010040000400400004000160000000004000040001600000,
  0x4000040000400000000040000400004000000014400004000040000000016000040000450000000040000400004000000000400004000040000000144000040001600000000040001000004500000000400004000040000000004000040000400000001440000400004000000001600004000045000000144000040000400000001440000400010000000000400004000160000000004000040001600000,
  0x4002040000400000040040000480004040000014480004000040000000016800040000450210000040020400004000000400400004800040000000144000040001600010000048001080004500000000400204000040000004004000048000404000001448000400004000000001680004000045021000144800040000400000041440000480010040000400400004000160000000004000040001600000,
  0x7800000000a80000000000000000000000000000001e0000000000000000000000000000000000000000000000a80000000000000000000000000000000000000000000a8000000000000000000780007800000000a80000000000000000000000000000001e000000000000000000000000000000000000001e00000000000000000000000000002a00000000000000000000000000a8000000000000000000,
  0x78060181efabc6018000180601800018069181e0181e01800f1bc6018000180601800f1806918000180601800fa8060180001806018000180601bc00180601800018060a80001bc6018000180607800078060181efabc60180001806018000180691bde0181e01800f1bc6018000180601800f1806918000181e01800f1bc60180001806018000182a01bc0018060180001bc6018000abc60180001806018000,
  0x7806018000a80601800018060180001806918000181e0180001806018000180601800018069180001806018000a80601800018060180001806018000180601800018060a8000180601800018060780007806018000a80601800018060180001806918000181e018000180601800018060180001806918000181e01800018060180001806018000182a01800018060180001806018000a8060180001806018000,
  0x78060181efabc6018000180601800018069181e0181e01800f1bc6018000180601800f1806918000180601800fa8060180001806018000180601bc00180601800018060a80001bc6018000180607800078060181efabc60180001806018000180691bde0181e01800f1bc6018000180601800f1806918000181e01800f1bc60180001806018000182a01bc0018060180001bc6018000abc60180001806018000,
  0x7806018000a80601800018060180001806018000181e0180001806018000180601800018060180001806018000a80601800018060180001806018000180601800018060a8000180601800018060780007806018000a80601800018060180001806018000181e018000180601800018060180001806018000181e01800018060180001806018000182a01800018060180001806018000a8060180001806018000,
  0x78060181efabc6018000180601800018069181e0181e01800f1bc6018000180601800f1806918000180601800fa8060180001806018000180601bc00180601800018060a80001bc6018000180607800078060181efabc60180001806018000180691bde0181e01800f1bc6018000180601800f1806918000181e01800f1bc60180001806018000182a01bc0018060180001bc6018000abc60180001806018000,
  0x7806018000a80601800018060180001806918000181e0180001806018000180601800018069180001806018000a80601800018060180001806018000180601800018060a8000180601800018060780007806018000a80601800018060180001806918000181e018000180601800018060180001806918000181e01800018060180001806018000182a01800018060180001806018000a8060180001806018000,
  0x78060181efabc6018000180601800018069181e0181e01800f1bc6018000180601800f1806918000180601800fa8060180001806018000180601bc00180601800018060a80001bc6018000180607800078060181efabc60180001806018000180691bde0181e01800f1bc6018000180601800f1806918000181e01800f1bc60180001806018000182a01bc0018060180001bc6018000abc60180001806018000,
  0x14000000000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000d00000000000000000140000000000000000000000014000000000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000d0000000000000000000000000000000000000140000000000000000000e,
  0x1d400002039c200002400020000200002700024000200002001c203802001c2000020000e00002001c200002039c20000240002000020000200002d000200002001c200014001c2001c2001c200002001d400002039c200002400020000200002700024000200002001c203802001c2000020000e000024000200002001c203802d00020000200002700024000200002001c203814039c200002001c27000e,
  0x14000020000200002400020000200002000024000200002000020000200002000020000e000020000200002000020000240002000020000200002d00020000200002000140000200002000020000200014000020000200002400020000200002000024000200002000020000200002000020000e0000240002000020000200002d0002000020000200002400020000200002000140000200002000020000e,
  0x1d400002039c200002400020000200002700024000200002001c203802001c2000020000e00002001c200002039c20000240002000020000200002d000200002001c200014001c2001c2001c200002001d400002039c200002400020000200002700024000200002001c203802001c2000020000e000024000200002001c203802d00020000200002700024000200002001c203814039c200002001c27000e,
  0x14000020000200002000020000200002000020000200002000020000200002000020000e000020000200002000020000200002000020000200002d00020000200002000140000200002000020000200014000020000200002000020000200002000020000200002000020000200002000020000e0000200002000020000200002d0002000020000200002000020000200002000140000200002000020000e,
  0x1d400002039c200002400020000200002700024000200002001c203802001c2000020000e00002001c200002039c20000240002000020000200002d000200002001c200014001c2001c2001c200002001d400002039c200002400020000200002700024000200002001c203802001c2000020000e000024000200002001c203802d00020000200002700024000200002001c203814039c200002001c27000e,
  0x14000020000200002400020000200002000024000200002000020000200002000020000e000020000200002000020000240002000020000200002d00020000200002000140000200002000020000200014000020000200002400020000200002000024000200002000020000200002000020000e0000240002000020000200002d0002000020000200002400020000200002000140000200002000020000e,
  0x1d400002039c200002400020000200002700024000200002001c203802001c2000020000e00002001c200002039c20000240002000020000200002d000200002001c200014001c2001c2001c200002001d400002039c200002400020000200002700024000200002001c203802001c2000020000e000024000200002001c203802d00020000200002700024000200002001c203814039c200002001c27000e
]

/-! ### States, the step and the check -/

/-- The block `000111`, letter `p` at phase `p`. -/
def w000111 : List Bool := [false, false, false, true, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `5 w .. 5 w + 4` of table
`8 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (8 * p + s) 0 >>> (5 * w)) % 32

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `11`, `101`, `1001`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 3) ||
    ((2 * s + b.toNat) % 8 == 5) ||
    ((2 * s + b.toNat) % 16 == 9)

/-- The last 3 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 8 else s

/-- The window of columns 1..8 after a step from phase `p`, with column 9 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 8 (w000111.getD p false) z w

/-- The certificate at one state: ranks are at most 26; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 6) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 6) (sNext p s w) (wNext p w true)
  decide (r ≤ 26) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 256

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 8 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 8 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 8 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 8 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 8 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 8 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 6 → allBelowT (partOK p) 8 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | p + 6, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 6) (hs : s < 8) (hw : w < 2 ^ 8) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 8 = 256 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 26 ∧
      (rk p s w = 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `000111` read from phase `ph`: letter `(t + ph) % 6` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w000111.getD ((t + ph) % 6) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..8` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 8
  | t + 1 => stripStep 8 (F t 0) (F t 9) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 8 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 8).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last three readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 6) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 8
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 8
    unfold sNext
    cases ((t + ph) % 6 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 8

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 6) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 9) := by
  show stripStep 8 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `26 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 26 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 9)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 6 = ((t + ph) % 6 + 1) % 6 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 26 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 26 ≤ t) (hp : (t + ph) % 6 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 6 = 0) :
    suf ph (drv (ctr ph) R) (t + 6) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 6) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  rw [h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_11 : ∀ s, s < 8 → badB (push s true) true = true := by decide
theorem bad_101 : ∀ s, s < 8 → badB (push (push s true) false) true = true := by decide
theorem bad_1001 : ∀ s, s < 8 → badB (push (push (push s true) false) false) true = true := by decide

end ReadingWords.B000111

open ReadingWords.B000111

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `11`.** At the first white steps, column 1 never reads `11` with the first reading at time `20` or
later. -/
theorem no_11_time_000111 (u : Nat) (hu : 20 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = true) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 6) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_11 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `101`.** At the first white steps, column 1 never reads `101` with the first reading at time `14` or
later. -/
theorem no_101_time_000111 (u : Nat) (hu : 14 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = false ∧ drv (ctr ph) R (u + 12) 1 = true) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 12 = u + 6 + 6 by omega] at h2
  have hb := no_bad R ph (u + 6 + 6) (by omega) (by omega)
  rw [suf_period R ph (u + 6) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_101 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `1001`.** At the first white steps, column 1 never reads `1001` with the first reading at time `8` or
later. -/
theorem no_1001_time_000111 (u : Nat) (hu : 8 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = false ∧ drv (ctr ph) R (u + 12) 1 = false ∧
      drv (ctr ph) R (u + 18) 1 = true) := by
  rintro ⟨h0, h1, h2, h3⟩
  rw [show u + 12 = u + 6 + 6 by omega] at h2
  rw [show u + 18 = u + 6 + 6 + 6 by omega] at h3
  have hb := no_bad R ph (u + 6 + 6 + 6) (by omega) (by omega)
  rw [suf_period R ph (u + 6 + 6) (by omega), suf_period R ph (u + 6) (by omega), suf_period R ph u hp, h0, h1, h2,
    h3] at hb
  rw [bad_1001 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B000111

/-- A sequence of bits has none of the factors `11`, `101`, `1001` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = false ∧ b (i + 3) = true)

/-- Column 1 of the right half driven by `000111` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 6 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (6 * i + (6 - ph % 6) % 6) 1

end ReadingWords.B000111

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`11`, `101`, `1001` from the 4th on. -/
theorem readings_000111 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 4 := by
  intro i hi
  have hp : (6 * i + (6 - ph % 6) % 6 + ph) % 6 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 6) 1 := by
    unfold reading; rw [show 6 * (i + 1) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 6 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 12) 1 := by
    unfold reading; rw [show 6 * (i + 2) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 12 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 18) 1 := by
    unfold reading; rw [show 6 * (i + 3) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 18 by omega]
  rw [e1, e2, e3]
  exact ⟨no_11_time_000111 R ph _ (by omega) hp, no_101_time_000111 R ph _ (by omega) hp,
    no_1001_time_000111 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `000111` -/

namespace ReadingWords.B000111

/-- From time `T` on, a row whose center column repeats `000111` from `T` has the right half driven by `000111` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w000111.getD ((t - T) % 6) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w000111.getD ((0 + 0) % 6) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w000111.getD ((t + 1 + 0) % 6) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B000111

/-- **Readings of every row.** If the center column of a row repeats `000111` from time `T` (letter
`(t - T) % 6` at time `t`), then column 1 at the times `T + 6 i` avoids `11`, `101`, `1001` from `i = 4` on. -/
theorem readings_000111_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w000111.getD ((t - T) % 6) false) :
    Avoids (fun i => evolve init (T + 6 * i) 1) 4 := by
  have e : (fun i => evolve init (T + 6 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 6 * i = T + (6 * i + (6 - 0 % 6) % 6) by omega]
    exact evolve_eq_drv init T h (6 * i + (6 - 0 % 6) % 6) 1
  rw [e]
  exact readings_000111 _ 0

end B000111

/-! ## Block `001101` -/

section B001101

/-! The certificate and the helpers live in `ReadingWords.B001101`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B001101

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `4 * p + s` packs the rank of window `w` in bits `5 w .. 5 w + 4`. -/
def rankTabs : List Nat := [
  0x1a000000000006800000000000000000000000001a000000680000000000000,
  0x80200802008020081a708020080206802008020080200802008020081a708020680200802008020,
  0x80200802008020081a008020080206802008020080200802008020081a008020680200802008020,
  0x80200802008020081a708020080206802008020080200802008020081a708020680200802008020,
  0x120000000000,
  0x60186000000000000000600060000003000000006018600000000000000060012600000000c,
  0x60000000000000000000600000000000000000006000000000000000000120000000000,
  0x60186000000000000000600060000003000000006018600000000000000060012600000000c,
  0x11000000000000000000000000000011000000001100000000000000000000000000000000000,
  0x11000005800502c000000500160000110000000011001605800502c005800500160000050000b,
  0x11000000000500000000050000000011000000001100000000050000000005000000000500000,
  0x11000005800502c000000500160000110000000011001605800502c005800500160000050000b,
  0x80000800000000000000000008000000000000008000080000000000000000000800008000000000,
  0x8000080000200000000a228008000020000000008280080000200000000a20000800008000000140,
  0x80000800002000000000200008000020000000008000080000200000000020000800008000000000,
  0x8000080000200000000a228008000020000000008280080000200000000a20000800008000000140,
  0xf0000000000000000000f0000000000000000000f000000000f,
  0x1230000000003000000000f0000002403000000012f0000000003000000000f000000000f,
  0x30000000003000000000f0000000003000000000f0000000003000000000f000000000f,
  0x1230000000003000000000f0000002403000000012f0000000003000000000f000000000f,
  0xe00000000000000e0000e00000000000000000000000000000000000,
  0x20000240002000020000e00002000020000e0000e00002400020000240002000020000200002,
  0x20000200002000020000e00002000020000e0000e00002000020000200002000020000200002,
  0x20000240002000020000e00002000020000e0000e00002400020000240002000020000200002
]

/-! ### States, the step and the check -/

/-- The block `001101`, letter `p` at phase `p`. -/
def w001101 : List Bool := [false, false, true, true, false, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `5 w .. 5 w + 4` of table
`4 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (4 * p + s) 0 >>> (5 * w)) % 32

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `11`, `101`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 3) ||
    ((2 * s + b.toNat) % 8 == 5)

/-- The last 2 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 4 else s

/-- The window of columns 1..6 after a step from phase `p`, with column 7 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 6 (w001101.getD p false) z w

/-- The certificate at one state: ranks are at most 18; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 6) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 6) (sNext p s w) (wNext p w true)
  decide (r ≤ 18) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 64

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 4 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 4 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 4 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 4 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 4 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 4 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 6 → allBelowT (partOK p) 4 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | p + 6, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 6) (hs : s < 4) (hw : w < 2 ^ 6) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 6 = 64 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 18 ∧
      (rk p s w = 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `001101` read from phase `ph`: letter `(t + ph) % 6` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w001101.getD ((t + ph) % 6) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..6` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 6
  | t + 1 => stripStep 6 (F t 0) (F t 7) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 6 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 6).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last two readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 6) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 4
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 4
    unfold sNext
    cases ((t + ph) % 6 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 4

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 6) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 7) := by
  show stripStep 6 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `18 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 18 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 7)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 6 = ((t + ph) % 6 + 1) % 6 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 18 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 18 ≤ t) (hp : (t + ph) % 6 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 6 = 0) :
    suf ph (drv (ctr ph) R) (t + 6) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 6) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  rw [h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_11 : ∀ s, s < 4 → badB (push s true) true = true := by decide
theorem bad_101 : ∀ s, s < 4 → badB (push (push s true) false) true = true := by decide

end ReadingWords.B001101

open ReadingWords.B001101

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `11`.** At the first white steps, column 1 never reads `11` with the first reading at time `12` or
later. -/
theorem no_11_time_001101 (u : Nat) (hu : 12 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = true) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 6) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_11 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `101`.** At the first white steps, column 1 never reads `101` with the first reading at time `6` or
later. -/
theorem no_101_time_001101 (u : Nat) (hu : 6 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = false ∧ drv (ctr ph) R (u + 12) 1 = true) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 12 = u + 6 + 6 by omega] at h2
  have hb := no_bad R ph (u + 6 + 6) (by omega) (by omega)
  rw [suf_period R ph (u + 6) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_101 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B001101

/-- A sequence of bits has none of the factors `11`, `101` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = true)

/-- Column 1 of the right half driven by `001101` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 6 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (6 * i + (6 - ph % 6) % 6) 1

end ReadingWords.B001101

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`11`, `101` from the 2th on. -/
theorem readings_001101 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 2 := by
  intro i hi
  have hp : (6 * i + (6 - ph % 6) % 6 + ph) % 6 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 6) 1 := by
    unfold reading; rw [show 6 * (i + 1) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 6 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 12) 1 := by
    unfold reading; rw [show 6 * (i + 2) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 12 by omega]
  rw [e1, e2]
  exact ⟨no_11_time_001101 R ph _ (by omega) hp, no_101_time_001101 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `001101` -/

namespace ReadingWords.B001101

/-- From time `T` on, a row whose center column repeats `001101` from `T` has the right half driven by `001101` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w001101.getD ((t - T) % 6) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w001101.getD ((0 + 0) % 6) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w001101.getD ((t + 1 + 0) % 6) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B001101

/-- **Readings of every row.** If the center column of a row repeats `001101` from time `T` (letter
`(t - T) % 6` at time `t`), then column 1 at the times `T + 6 i` avoids `11`, `101` from `i = 2` on. -/
theorem readings_001101_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w001101.getD ((t - T) % 6) false) :
    Avoids (fun i => evolve init (T + 6 * i) 1) 2 := by
  have e : (fun i => evolve init (T + 6 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 6 * i = T + (6 * i + (6 - 0 % 6) % 6) by omega]
    exact evolve_eq_drv init T h (6 * i + (6 - 0 % 6) % 6) 1
  rw [e]
  exact readings_001101 _ 0

end B001101

/-! ## Block `010111` -/

section B010111

/-! The certificate and the helpers live in `ReadingWords.B010111`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B010111

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `8 * p + s` packs the rank of window `w` in bits `5 w .. 5 w + 4`. -/
def rankTabs : List Nat := [
  0x260000000000000000000000000000000000000026000000000000000000000,
  0x1a0000e0001a068260681a0001a0001a0681a0681a0001a0001a068260001a0001a0001a0681a0,
  0x260000000000000000000000000000000000000026000000000000000000000,
  0x81a009ce0081a068260681a009da009da069da0681a009da0081a068260081a009da009da069da0,
  0x260000000000000000000000000000000000000026000000000000000000000,
  0x1a0000e0001a068260681a0001a0001a0681a0681a0001a0001a068260001a0001a0001a0681a0,
  0x8020080200802008260080200802008020080200802008020080200826008020080200802008020,
  0x81a009ce0081a068260681a009da009da069da0681a009da0081a068260081a009da009da069da0,
  0x0,
  0x900000000000000000009000090000000000000090000000000000000000900009000000000,
  0x0,
  0x6018c900003318c6000c60180900009018c601806018c900003318c6000c3318c900009018c60000,
  0x0,
  0x900000000000000000009000090000000000000090000000000000000000900009000000000,
  0x300003000000000000003000030000000000000030000300000000030000300003000000000,
  0x6018c900003318c6000c60180900009018c601806018c900003318c6000c3318c900009018c60000,
  0x0,
  0x110000000000000000001100000000000000000011000000000000000000110000000000,
  0x0,
  0x5800b580115800b02c055800b001710000b0000b5800b581715800b02c055800b001715800b0000b,
  0x0,
  0x110000000000000000001100000000000000000011000000000000000000110000000000,
  0x50000000005000000000500000000000000000005000000000500000000050000000000,
  0x5800b580115800b02c055800b001710000b0000b5800b581715800b02c055800b001715800b0000b,
  0x1600000,
  0x10000000001000000000100000000010000000001000000000100000000010000100001600000,
  0x1600000,
  0x5281002804028100294a5001002804028100014a5281002804028100294a0281002950028160294a,
  0x1600000,
  0x10000000001000000000100000000010000000001000000000100000000010000100001600000,
  0x4000040000400000000040000400004000000000400004000040000000004000040001600000,
  0x5281002804028100294a5001002804028100014a5281002804028100294a0281002950028160294a,
  0xa8000000000000000000a800000000000000000000000000000000000000,
  0x781e0780007800000000a8000780007800000000a81e078000780000000078000780007800078000,
  0xa8000000000000000000a800000000000000000000000000000000000000,
  0x7a5e07a400780601a520a80607a5207a46018009aa5e07a520780601a520780607a5207a4607a529,
  0xa8000000000000000000a800000000000000000000000000000000000000,
  0x781e0780007800000000a8000780007800000000a81e078000780000000078000780007800078000,
  0x18060180001806018000a8060180001806018000a806018000180601800018060180001806018000,
  0x7a5e07a400780601a520a80607a5207a46018009aa5e07a520780601a520780607a5207a4607a529,
  0x140000000000000000000000000000000000000000,
  0xe000000000e000000000e0000000014000000000e000000000e000000000e0000e0000e,
  0x140000000000000000000000000000000000000000,
  0x20020200e000020010e020020200e0200200014020020200e000020010e000020200e0200e0210e,
  0x140000000000000000000000000000000000000000,
  0xe000000000e000000000e0000000014000000000e000000000e000000000e0000e0000e,
  0x2000020000200002000020000200002000140000200002000020000200002000020000200002,
  0x20020200e000020010e020020200e0200200014020020200e000020010e000020200e0200e0210e
]

/-! ### States, the step and the check -/

/-- The block `010111`, letter `p` at phase `p`. -/
def w010111 : List Bool := [false, true, false, true, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `5 w .. 5 w + 4` of table
`8 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (8 * p + s) 0 >>> (5 * w)) % 32

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `111`, `1101`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 8 == 7) ||
    ((2 * s + b.toNat) % 16 == 13)

/-- The last 3 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 8 else s

/-- The window of columns 1..6 after a step from phase `p`, with column 7 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 6 (w010111.getD p false) z w

/-- The certificate at one state: ranks are at most 22; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 6) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 6) (sNext p s w) (wNext p w true)
  decide (r ≤ 22) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 64

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 8 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 8 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 8 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 8 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 8 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 8 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 6 → allBelowT (partOK p) 8 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | p + 6, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 6) (hs : s < 8) (hw : w < 2 ^ 6) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 6 = 64 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 22 ∧
      (rk p s w = 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 6) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `010111` read from phase `ph`: letter `(t + ph) % 6` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w010111.getD ((t + ph) % 6) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..6` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 6
  | t + 1 => stripStep 6 (F t 0) (F t 7) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 6 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 6).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last three readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 6) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 8
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 8
    unfold sNext
    cases ((t + ph) % 6 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 8

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 6) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 7) := by
  show stripStep 6 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `22 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 22 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 7)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 6 = ((t + ph) % 6 + 1) % 6 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 6) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 22 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 22 ≤ t) (hp : (t + ph) % 6 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 6 = 0) :
    suf ph (drv (ctr ph) R) (t + 6) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 6) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 6) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  rw [h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_111 : ∀ s, s < 8 → badB (push (push s true) true) true = true := by decide
theorem bad_1101 : ∀ s, s < 8 → badB (push (push (push s true) true) false) true = true := by decide

end ReadingWords.B010111

open ReadingWords.B010111

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `111`.** At the first white steps, column 1 never reads `111` with the first reading at time `10` or
later. -/
theorem no_111_time_010111 (u : Nat) (hu : 10 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = true ∧ drv (ctr ph) R (u + 12) 1 = true) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 12 = u + 6 + 6 by omega] at h2
  have hb := no_bad R ph (u + 6 + 6) (by omega) (by omega)
  rw [suf_period R ph (u + 6) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_111 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `1101`.** At the first white steps, column 1 never reads `1101` with the first reading at time `4` or
later. -/
theorem no_1101_time_010111 (u : Nat) (hu : 4 ≤ u) (hp : (u + ph) % 6 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 6) 1 = true ∧ drv (ctr ph) R (u + 12) 1 = false ∧
      drv (ctr ph) R (u + 18) 1 = true) := by
  rintro ⟨h0, h1, h2, h3⟩
  rw [show u + 12 = u + 6 + 6 by omega] at h2
  rw [show u + 18 = u + 6 + 6 + 6 by omega] at h3
  have hb := no_bad R ph (u + 6 + 6 + 6) (by omega) (by omega)
  rw [suf_period R ph (u + 6 + 6) (by omega), suf_period R ph (u + 6) (by omega), suf_period R ph u hp, h0, h1, h2,
    h3] at hb
  rw [bad_1101 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B010111

/-- A sequence of bits has none of the factors `111`, `1101` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true ∧ b (i + 2) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = true ∧ b (i + 2) = false ∧ b (i + 3) = true)

/-- Column 1 of the right half driven by `010111` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 6 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (6 * i + (6 - ph % 6) % 6) 1

end ReadingWords.B010111

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`111`, `1101` from the 2th on. -/
theorem readings_010111 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 2 := by
  intro i hi
  have hp : (6 * i + (6 - ph % 6) % 6 + ph) % 6 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 6) 1 := by
    unfold reading; rw [show 6 * (i + 1) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 6 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 12) 1 := by
    unfold reading; rw [show 6 * (i + 2) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 12 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (6 * i + (6 - ph % 6) % 6 + 18) 1 := by
    unfold reading; rw [show 6 * (i + 3) + (6 - ph % 6) % 6 = 6 * i + (6 - ph % 6) % 6 + 18 by omega]
  rw [e1, e2, e3]
  exact ⟨no_111_time_010111 R ph _ (by omega) hp, no_1101_time_010111 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `010111` -/

namespace ReadingWords.B010111

/-- From time `T` on, a row whose center column repeats `010111` from `T` has the right half driven by `010111` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w010111.getD ((t - T) % 6) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w010111.getD ((0 + 0) % 6) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w010111.getD ((t + 1 + 0) % 6) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B010111

/-- **Readings of every row.** If the center column of a row repeats `010111` from time `T` (letter
`(t - T) % 6` at time `t`), then column 1 at the times `T + 6 i` avoids `111`, `1101` from `i = 2` on. -/
theorem readings_010111_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w010111.getD ((t - T) % 6) false) :
    Avoids (fun i => evolve init (T + 6 * i) 1) 2 := by
  have e : (fun i => evolve init (T + 6 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 6 * i = T + (6 * i + (6 - 0 % 6) % 6) by omega]
    exact evolve_eq_drv init T h (6 * i + (6 - 0 % 6) % 6) 1
  rw [e]
  exact readings_010111 _ 0

end B010111

/-! ## Block `0000001` -/

section B0000001

/-! The certificate and the helpers live in `ReadingWords.B0000001`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B0000001

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `8 * p + s` packs the rank of window `w` in bits `6 w .. 6 w + 5`. -/
def rankTabs : List Nat := [
  0x44000300001100000a0000000000037c000000001801100000000300001100001800000000000300000000000a00000000000300000044000a00000000000300000000000344000000000300000001100300000000000300000000044300000000001800000000000a0000004400037d10000000030110000000030000000000030000000004430000000000030000000000180000110000034400000000037c000000001800000000000300000000000300000044000300001100000300000000000300001100001f00000044000300000000000301100000000300001100045800000000000300000000000a00000000000300000000000a0000000000030000000000030000000000030000110000030000117c000300000000000300000000000300000044001f0000000000030000000000180000000000180000110000030000117c000300000000000301100000000300000000000344000000000300000000001800000044000300001100045800000000000300000000000300000044000300001100001f0000004400037c000000001801100000000300001100045800000000000300000000000a00000000000300000044000a0000000000030000000000034400000000030000110110030000117c000300000000044300000000001800000000000a0000004400037d10000000030110000000030000000000030000000004430000000000030000000000180000110000034400000000037c000000001800000000000300000000000300000044000300001100000300000000001800000000000a0000004400037d100000000301100000000300000000000300000000044300000000000300000000000300000044001f0000000000030000000000184400000000030000110000030000117c000300000000000300000000000300000044000a000000000003000000000003011000000018000011000003000011000443000000000003011000000003000011000458000000000003000000000018000000440003000011000003000011000003440011000018,
  0xa0000000000007c000000001800000000000000000000001800000028000000000000000a00000a00000000000000000a00000000000028000000000000000000000000000000000000000028000000000000000000000a00001800000000000a0000000000007c00000000000000000000000000000000000000002800000000000000000000000000180000000000000000000000007c000000001800000000000000000000000000000000000000000000000000000000000000000000001f00000000000028000000000000000000000000000000001800000028000000000000000a00000a00000000000000000a0000000000002800000000000000000000000000000000000000007c000000000000000000000a00000000000000001f0000000000002800000000180000000000180000000000000000007c000000000000000000000000000000000000000000000000000028000000001800000000000000000000001800000000000000000000000000000000000000000000001f0000000000007c000000001800000000000000000000001800000028000000000000000a00000a00000000000000000a0000000000002800000000000000000000000000000000000000007c000000000000000000000a00001800000000000a0000000000007c00000000000000000000000000000000000000002800000000000000000000000000180000000000000000000000007c000000001800000000000000000000000000000000000000000000000000000a00001800000000000a0000000000007c000000000000000000000000000000000000000028000000000000000000000a00000000000000001f0000000000002800000000180000000000000000000000000000007c000000000000000000000a00000000000000000a000000000000280000000000000000000018000000000000000000280000000000000000000000000000000000000018000000000000280000000018000000000000000000000000000000000000000000000018,
  0x44000300001100000a0000000000037c000000001801100000000300001100001800000000000300000000000a00000000000300000044000a00000000000300000000000344000000000300000001100300000000000300000000044300000000001800000000000a0000004400037d10000000030110000000030000000000030000000004430000000000030000000000180000110000034400000000037c000000001800000000000300000000000300000044000300001100000300000000000300001100001f00000044000300000000000301100000000300001100045800000000000300000000000a00000000000300000000000a0000000000030000000000030000000000030000110000030000117c000300000000000300000000000300000044001f0000000000030000000000180000000000180000110000030000117c000300000000000301100000000300000000000344000000000300000000001800000044000300001100045800000000000300000000000300000044000300001100001f0000004400037c000000001801100000000300001100045800000000000300000000000a00000000000300000044000a0000000000030000000000034400000000030000110110030000117c000300000000044300000000001800000000000a0000004400037d10000000030110000000030000000000030000000004430000000000030000000000180000110000034400000000037c000000001800000000000300000000000300000044000300001100000300000000001800000000000a0000004400037d100000000301100000000300000000000300000000044300000000000300000000000300000044001f0000000000030000000000184400000000030000110000030000117c000300000000000300000000000300000044000a000000000003000000000003011000000018000011000003000011000443000000000003011000000003000011000458000000000003000000000018000000440003000011000003000011000003440011000018,
  0x300000000000a0000000000037c000000001800000000000300000000001800000000000300000000000a00000000000300000000000a00000000000300000000000300000000000300000000000300000000000300000000000300000000001800000000000a0000000000037c00000000030000000000030000000000030000000000030000000000030000000000180000000000030000000000037c000000001800000000000300000000000300000000000300000000000300000000000300000000001f00000000000300000000000300000000000300000000001800000000000300000000000a00000000000300000000000a0000000000030000000000030000000000030000000000030000007c000300000000000300000000000300000000001f0000000000030000000000180000000000180000000000030000007c000300000000000300000000000300000000000300000000000300000000001800000000000300000000001800000000000300000000000300000000000300000000001f0000000000037c000000001800000000000300000000001800000000000300000000000a00000000000300000000000a0000000000030000000000030000000000030000000000030000007c000300000000000300000000001800000000000a0000000000037c00000000030000000000030000000000030000000000030000000000030000000000180000000000030000000000037c000000001800000000000300000000000300000000000300000000000300000000001800000000000a0000000000037c000000000300000000000300000000000300000000000300000000000300000000000300000000001f0000000000030000000000180000000000030000000000030000007c000300000000000300000000000300000000000a000000000003000000000003000000000018000000000003000000000003000000000003000000000003000000000018000000000003000000000018000000000003000000000003000000000003000000000018,
  0x44000300001100000a0000000000037c000000001801100000000300001100001800000000000300000000000a00000000000300000044000a00000000000300000000000344000000000300000001100300000000000300000000044300000000001800000000000a0000004400037d10000000030110000000030000000000030000000004430000000000030000000000180000110000034400000000037c000000001800000000000300000000000300000044000300001100000300000000000300001100001f00000044000300000000000301100000000300001100045800000000000300000000000a00000000000300000000000a0000000000030000000000030000000000030000110000030000117c000300000000000300000000000300000044001f0000000000030000000000180000000000180000110000030000117c000300000000000301100000000300000000000344000000000300000000001800000044000300001100045800000000000300000000000300000044000300001100001f0000004400037c000000001801100000000300001100045800000000000300000000000a00000000000300000044000a0000000000030000000000034400000000030000110110030000117c000300000000044300000000001800000000000a0000004400037d10000000030110000000030000000000030000000004430000000000030000000000180000110000034400000000037c000000001800000000000300000000000300000044000300001100000300000000001800000000000a0000004400037d100000000301100000000300000000000300000000044300000000000300000000000300000044001f0000000000030000000000184400000000030000110000030000117c000300000000000300000000000300000044000a000000000003000000000003011000000018000011000003000011000443000000000003011000000003000011000458000000000003000000000018000000440003000011000003000011000003440011000018,
  0xa0000000000007c000000001800000000000000000000001800000028000000000000000a00000a00000000000000000a00000000000028000000000000000000000000000000000000000028000000000000000000000a00001800000000000a0000000000007c00000000000000000000000000000000000000002800000000000000000000000000180000000000000000000000007c000000001800000000000000000000000000000000000000000000000000000000000000000000001f00000000000028000000000000000000000000000000001800000028000000000000000a00000a00000000000000000a0000000000002800000000000000000000000000000000000000007c000000000000000000000a00000000000000001f0000000000002800000000180000000000180000000000000000007c000000000000000000000000000000000000000000000000000028000000001800000000000000000000001800000000000000000000000000000000000000000000001f0000000000007c000000001800000000000000000000001800000028000000000000000a00000a00000000000000000a0000000000002800000000000000000000000000000000000000007c000000000000000000000a00001800000000000a0000000000007c00000000000000000000000000000000000000002800000000000000000000000000180000000000000000000000007c000000001800000000000000000000000000000000000000000000000000000a00001800000000000a0000000000007c000000000000000000000000000000000000000028000000000000000000000a00000000000000001f0000000000002800000000180000000000000000000000000000007c000000000000000000000a00000000000000000a000000000000280000000000000000000018000000000000000000280000000000000000000000000000000000000018000000000000280000000018000000000000000000000000000000000000000000000018,
  0x44000300001100000a0000000000037c000000001801100000000300001100001800000000000300000000000a00000000000300000044000a00000000000300000000000344000000000300000001100300000000000300000000044300000000001800000000000a0000004400037d10000000030110000000030000000000030000000004430000000000030000000000180000110000034400000000037c000000001800000000000300000000000300000044000300001100000300000000000300001100001f00000044000300000000000301100000000300001100045800000000000300000000000a00000000000300000000000a0000000000030000000000030000000000030000110000030000117c000300000000000300000000000300000044001f0000000000030000000000180000000000180000110000030000117c000300000000000301100000000300000000000344000000000300000000001800000044000300001100045800000000000300000000000300000044000300001100001f0000004400037c000000001801100000000300001100045800000000000300000000000a00000000000300000044000a0000000000030000000000034400000000030000110110030000117c000300000000044300000000001800000000000a0000004400037d10000000030110000000030000000000030000000004430000000000030000000000180000110000034400000000037c000000001800000000000300000000000300000044000300001100000300000000001800000000000a0000004400037d100000000301100000000300000000000300000000044300000000000300000000000300000044001f0000000000030000000000184400000000030000110000030000117c000300000000000300000000000300000044000a000000000003000000000003011000000018000011000003000011000443000000000003011000000003000011000458000000000003000000000018000000440003000011000003000011000003440011000018,
  0xa0000000000007c000000001800000000000000000000001800000000000000000000000a00000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000001800000000000a0000000000007c00000000000000000000000000000000000000000000000000000000000000000000180000000000000000000000007c000000001800000000000000000000000000000000000000000000000000000000000000000000001f00000000000000000000000000000000000000000000001800000000000000000000000a00000000000000000000000a0000000000000000000000000000000000000000000000000000007c000000000000000000000000000000000000001f0000000000000000000000180000000000180000000000000000007c000000000000000000000000000000000000000000000000000000000000001800000000000000000000001800000000000000000000000000000000000000000000001f0000000000007c000000001800000000000000000000001800000000000000000000000a00000000000000000000000a0000000000000000000000000000000000000000000000000000007c000000000000000000000000001800000000000a0000000000007c00000000000000000000000000000000000000000000000000000000000000000000180000000000000000000000007c000000001800000000000000000000000000000000000000000000000000000000001800000000000a0000000000007c000000000000000000000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000180000000000000000000000000000007c000000000000000000000000000000000000000a000000000000000000000000000000000018000000000000000000000000000000000000000000000000000000000018000000000000000000000018000000000000000000000000000000000000000000000018,
  0x200078201000201001700000200000900000201e40200000200078201000200001700001700001e00001700000200000200000200001700001700000200000900000200000900040200041e00000200000200000200001e00000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000240079701000200000200040200040900001701e00900000200000900001700000200001700000900000200000200000200000201000201000200000200000900000200000200000200078201000200001700001700000900001700000200000200000200001700000200000200000900000200000900000200040900000200000201000200001e00000200000200000200000200000200000200000200000900000201e00900000240079701000200000200000200001e00001740001700000200000200000200000200040200041e00000200000900000200001e01000200001700000200000900001700000200000200078201000201001700000200000900000201e40200000200078201000200001700001700001e00001700000200000200000200001700001700000200000900000200000900040200041e00000200000201000200001e00000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000240079701000200000200040200040900001701e00900000200000900001700000200001700000900000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000200000200001700000200000200000900000201e00900040200040900000200000201000200001e40000200002500000200000200001700001700000200000900000200000900000200079701000200000200000200001e00001740000200000200078201000200001700000200000900000201e00900000200000901000200000201000200041e000002000017,
  0x78000000000001700000000000900000001e00000000000978000000000001700001700001e00001700900000000000924000001700001700000000000900000000900900000000001e00000000000000000000001e00900000000000000000024000000000001700000000001e00000000900000000000924000000000000000000000001000001700900000000000979700000000000000000000000900001701e00900000000000900001700000000001700000900900000000000000000024000000000000000000000000900000000900000000000978000000000001700001700000900001700900000000000924000001700000000000000000900000000900900000000000900000000000000000000001e00900000000000000000924000000000000000000000000900000001e00900000000979700000000000000000000001e00001700901700000000924000000000000000000000001e00000000900900000000001e00000000001700000000000900001700000000000000078000000000001700000000000900000001e00000000000978000000000001700001700001e00001700900000000000924000001700001700000000000900000000900900000000001e00000000000000000000001e00900000000000000000024000000000001700000000001e00000000900000000000924000000000000000000000001000001700900000000000979700000000000000000000000900001701e00900000000000900001700000000001700000900900000000000000000024000000000001700000000001e00000000900000000000924000000000000000000000001000001700900000000000924000001700000000000000000900000001e00900000000000900000000000000000000001e00900000002500000000924000001700001700000000000900000000900900000000979700000000000000000000001e00001700900000000000978000000000001700000000000900000001e00900000000000900000000000000000000001e000000000017,
  0x200078201000201001700000200000900000201e40200000200078201000200001700001700001e00001700000200000200000200001700001700000200000900000200000900040200041e00000200000200000200001e00000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000240079701000200000200040200040900001701e00900000200000900001700000200001700000900000200000200000200000201000201000200000200000900000200000200000200078201000200001700001700000900001700000200000200000200001700000200000200000900000200000900000200040900000200000201000200001e00000200000200000200000200000200000200000200000900000201e00900000240079701000200000200000200001e00001740001700000200000200000200000200040200041e00000200000900000200001e01000200001700000200000900001700000200000200078201000201001700000200000900000201e40200000200078201000200001700001700001e00001700000200000200000200001700001700000200000900000200000900040200041e00000200000201000200001e00000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000240079701000200000200040200040900001701e00900000200000900001700000200001700000900000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000200000200001700000200000200000900000201e00900040200040900000200000201000200001e40000200002500000200000200001700001700000200000900000200000900000200079701000200000200000200001e00001740000200000200078201000200001700000200000900000201e00900000200000901000200000201000200041e000002000017,
  0x200078200000200001700000200000900000201e00200000200078200000200001700001700001e00001700000200000200000200001700001700000200000900000200000900000200001e00000200000200000200001e00000200000200000200000200000200001700000200001e00000200000200000200000200000200000200000200001000001700000200000200079700000200000200000200000900001701e00900000200000900001700000200001700000900000200000200000200000200000200000200000200000900000200000200000200078200000200001700001700000900001700000200000200000200001700000200000200000900000200000900000200000900000200000200000200001e00000200000200000200000200000200000200000200000900000201e00900000200079700000200000200000200001e00001700001700000200000200000200000200000200001e00000200000900000200001e00000200001700000200000900001700000200000200078200000200001700000200000900000201e00200000200078200000200001700001700001e00001700000200000200000200001700001700000200000900000200000900000200001e00000200000200000200001e00000200000200000200000200000200001700000200001e00000200000200000200000200000200000200000200001000001700000200000200079700000200000200000200000900001701e00900000200000900001700000200001700000900000200000200000200000200000200001700000200001e00000200000200000200000200000200000200000200001000001700000200000200000200001700000200000200000900000201e00900000200000900000200000200000200001e00000200002500000200000200001700001700000200000900000200000900000200079700000200000200000200001e00001700000200000200078200000200001700000200000900000201e00900000200000900000200000200000200001e000002000017,
  0x200078201000201001700000200000900000201e40200000200078201000200001700001700001e00001700000200000200000200001700001700000200000900000200000900040200041e00000200000200000200001e00000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000240079701000200000200040200040900001701e00900000200000900001700000200001700000900000200000200000200000201000201000200000200000900000200000200000200078201000200001700001700000900001700000200000200000200001700000200000200000900000200000900000200040900000200000201000200001e00000200000200000200000200000200000200000200000900000201e00900000240079701000200000200000200001e00001740001700000200000200000200000200040200041e00000200000900000200001e01000200001700000200000900001700000200000200078201000201001700000200000900000201e40200000200078201000200001700001700001e00001700000200000200000200001700001700000200000900000200000900040200041e00000200000201000200001e00000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000240079701000200000200040200040900001701e00900000200000900001700000200001700000900000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000200000200001700000200000200000900000201e00900040200040900000200000201000200001e40000200002500000200000200001700001700000200000900000200000900000200079701000200000200000200001e00001740000200000200078201000200001700000200000900000201e00900000200000901000200000201000200041e000002000017,
  0x78000000000001700000000000900000001e00000000000978000000000001700001700001e00001700900000000000924000001700001700000000000900000000900900000000001e00000000000000000000001e00900000000000000000024000000000001700000000001e00000000900000000000924000000000000000000000001000001700900000000000979700000000000000000000000900001701e00900000000000900001700000000001700000900900000000000000000024000000000000000000000000900000000900000000000978000000000001700001700000900001700900000000000924000001700000000000000000900000000900900000000000900000000000000000000001e00900000000000000000924000000000000000000000000900000001e00900000000979700000000000000000000001e00001700901700000000924000000000000000000000001e00000000900900000000001e00000000001700000000000900001700000000000000078000000000001700000000000900000001e00000000000978000000000001700001700001e00001700900000000000924000001700001700000000000900000000900900000000001e00000000000000000000001e00900000000000000000024000000000001700000000001e00000000900000000000924000000000000000000000001000001700900000000000979700000000000000000000000900001701e00900000000000900001700000000001700000900900000000000000000024000000000001700000000001e00000000900000000000924000000000000000000000001000001700900000000000924000001700000000000000000900000001e00900000000000900000000000000000000001e00900000002500000000924000001700001700000000000900000000900900000000979700000000000000000000001e00001700900000000000978000000000001700000000000900000001e00900000000000900000000000000000000001e000000000017,
  0x200078201000201001700000200000900000201e40200000200078201000200001700001700001e00001700000200000200000200001700001700000200000900000200000900040200041e00000200000200000200001e00000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000240079701000200000200040200040900001701e00900000200000900001700000200001700000900000200000200000200000201000201000200000200000900000200000200000200078201000200001700001700000900001700000200000200000200001700000200000200000900000200000900000200040900000200000201000200001e00000200000200000200000200000200000200000200000900000201e00900000240079701000200000200000200001e00001740001700000200000200000200000200040200041e00000200000900000200001e01000200001700000200000900001700000200000200078201000201001700000200000900000201e40200000200078201000200001700001700001e00001700000200000200000200001700001700000200000900000200000900040200041e00000200000201000200001e00000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000240079701000200000200040200040900001701e00900000200000900001700000200001700000900000200000240000200000200000200001700000200001e00000200040200000200000200000200000200000200001000001740000200000200000200001700000200000200000900000201e00900040200040900000200000201000200001e40000200002500000200000200001700001700000200000900000200000900000200079701000200000200000200001e00001740000200000200078201000200001700000200000900000201e00900000200000901000200000201000200041e000002000017,
  0x78000000000001700000000000900000001e00000000000078000000000001700001700001e00001700000000000000000000001700001700000000000900000000000900000000001e00000000000000000000001e00000000000000000000000000000000001700000000001e00000000000000000000000000000000000000000000001000001700000000000000079700000000000000000000000900001701e00900000000000900001700000000001700000900000000000000000000000000000000000000000000000900000000000000000000078000000000001700001700000900001700000000000000000000001700000000000000000900000000000900000000000900000000000000000000001e00000000000000000000000000000000000000000000000900000001e00900000000079700000000000000000000001e00001700001700000000000000000000000000000000001e00000000000900000000001e00000000001700000000000900001700000000000000078000000000001700000000000900000001e00000000000078000000000001700001700001e00001700000000000000000000001700001700000000000900000000000900000000001e00000000000000000000001e00000000000000000000000000000000001700000000001e00000000000000000000000000000000000000000000001000001700000000000000079700000000000000000000000900001701e00900000000000900001700000000001700000900000000000000000000000000000000001700000000001e00000000000000000000000000000000000000000000001000001700000000000000000000001700000000000000000900000001e00900000000000900000000000000000000001e00000000002500000000000000001700001700000000000900000000000900000000079700000000000000000000001e00001700000000000000078000000000001700000000000900000001e00900000000000900000000000000000000001e000000000017,
  0x1601d0010017410010010080160080010160013c100101600101d0010017410013d60017410160013c100101600102400101d00100175600100100801600800101600100100100101600800100100100100100100100100100100100100100100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100101d0010160010013d600101601d0010160010160010010160080010167410160010010160010010010010010013c101601d0010010010010010083d600800100100100100100100101d0010010010013d600174101600100100101600100100100800100101600100100801600800101600100100100100100800100175600100100100100100100100100100100100100800100101600100100801600800101600100100100100101d0010160010013d600175600100100100101600100100101d0010010010010160010160080010010010010160013d601d0010017410013d600100100100101600101600100101601d0010017410010010083d60080010160013c100101600101d0010017410013d60017410160013c100101600102400101d00100175600100100801600800101600100100100101600800100175600100100100100100100100100100100100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100101d0010160010013d600101601d0010160010160010010160080010167410160010010160010010010010010013c100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100100800100101600100100801600800101600100100100101601d00101675600101600100100100100100100100100100101d00100175600100100801600800101600100100100100101d0010160010013d600175600100100100101600100100101d0010017410013d60010160080010160010010010013d60080010160010013d6001741001001016001001001016,
  0x1601d00000074000000000801600800001620000000001600001d00000074000001600074001620000000001600002400001d00000075600000000801600800001620000000000001600800000020000000000020000020000000000000000000000f00000020000000000801601d00000020000000000000001d00000020000001600020000020000000001600000000001d00001620000001600001601d00001620001600000001600800001674001600000021600000000000000000000001601d00000020000000000801600800000020000000000000001d00000020000001600074001620000000001600000000000800000021600000000801600800001620000000000000000800000075600000000020000020000000000000000000000800000021600000000801600800001620000000000000001d00001620000001600075600020000000001600000000001d00000020000001600001600800000020000001600001601d00000074000001600020000000001600001600000001601d00000074000000000801600800001620000000001600001d00000074000001600074001620000000001600002400001d00000075600000000801600800001620000000000001600800000075600000000020000020000000000000000000000f00000020000000000801601d00000020000000000000001d00000020000001600020000020000000001600000000001d00001620000001600001601d00001620001600000001600800001674001600000021600000000000000000000000000f00000020000000000801601d00000020000000000000001d00000020000001600020000020000000001600000000000800000021600000000801600800001620000000000001601d00001675600001600020000020000000000000000000001d00000075600000000801600800001620000000000000001d00001620000001600075600020000000001600000000001d000000740000016000016008000016200000000000016008000016200000016000740000000016000000000016,
  0x1601d0010017410010010080160080010160013c100101600101d0010017410013d60017410160013c100101600102400101d00100175600100100801600800101600100100100101600800100100100100100100100100100100100100100100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100101d0010160010013d600101601d0010160010160010010160080010167410160010010160010010010010010013c101601d0010010010010010083d600800100100100100100100101d0010010010013d600174101600100100101600100100100800100101600100100801600800101600100100100100100800100175600100100100100100100100100100100100100800100101600100100801600800101600100100100100101d0010160010013d600175600100100100101600100100101d0010010010010160010160080010010010010160013d601d0010017410013d600100100100101600101600100101601d0010017410010010083d60080010160013c100101600101d0010017410013d60017410160013c100101600102400101d00100175600100100801600800101600100100100101600800100175600100100100100100100100100100100100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100101d0010160010013d600101601d0010160010160010010160080010167410160010010160010010010010010013c100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100100800100101600100100801600800101600100100100101601d00101675600101600100100100100100100100100100101d00100175600100100801600800101600100100100100101d0010160010013d600175600100100100101600100100101d0010017410013d60010160080010160010010010013d60080010160010013d6001741001001016001001001016,
  0x1601d00100174100100100801600800101600100100101600101d00100174100101600174101600100100101600102400101d00100175600100100801600800101600100100100101600800100100100100100100100100100100100100100100100f00100100100100100801601d00100100100100100100101d00100100100101600100100100100100101600100100101d00101600100101600101601d00101600101600100101600800101674101600100101600100100100100100100101601d00100100100100100801600800100100100100100100101d00100100100101600174101600100100101600100100100800100101600100100801600800101600100100100100100800100175600100100100100100100100100100100100100800100101600100100801600800101600100100100100101d00101600100101600175600100100100101600100100101d00100100100101600101600800100100100101600101601d00100174100101600100100100101600101600100101601d00100174100100100801600800101600100100101600101d00100174100101600174101600100100101600102400101d00100175600100100801600800101600100100100101600800100175600100100100100100100100100100100100100f00100100100100100801601d00100100100100100100101d00100100100101600100100100100100101600100100101d00101600100101600101601d00101600101600100101600800101674101600100101600100100100100100100100100f00100100100100100801601d00100100100100100100101d00100100100101600100100100100100101600100100100800100101600100100801600800101600100100100101601d00101675600101600100100100100100100100100100101d00100175600100100801600800101600100100100100101d00101600100101600175600100100100101600100100101d001001741001016001016008001016001001001001016008001016001001016001741001001016001001001016,
  0x1601d0010017410010010080160080010160013c100101600101d0010017410013d60017410160013c100101600102400101d00100175600100100801600800101600100100100101600800100100100100100100100100100100100100100100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100101d0010160010013d600101601d0010160010160010010160080010167410160010010160010010010010010013c101601d0010010010010010083d600800100100100100100100101d0010010010013d600174101600100100101600100100100800100101600100100801600800101600100100100100100800100175600100100100100100100100100100100100100800100101600100100801600800101600100100100100101d0010160010013d600175600100100100101600100100101d0010010010010160010160080010010010010160013d601d0010017410013d600100100100101600101600100101601d0010017410010010083d60080010160013c100101600101d0010017410013d60017410160013c100101600102400101d00100175600100100801600800101600100100100101600800100175600100100100100100100100100100100100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100101d0010160010013d600101601d0010160010160010010160080010167410160010010160010010010010010013c100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100100800100101600100100801600800101600100100100101601d00101675600101600100100100100100100100100100101d00100175600100100801600800101600100100100100101d0010160010013d600175600100100100101600100100101d0010017410013d60010160080010160010010010013d60080010160010013d6001741001001016001001001016,
  0x1601d00000074000000000801600800001620000000001600001d00000074000001600074001620000000001600002400001d00000075600000000801600800001620000000000001600800000020000000000020000020000000000000000000000f00000020000000000801601d00000020000000000000001d00000020000001600020000020000000001600000000001d00001620000001600001601d00001620001600000001600800001674001600000021600000000000000000000001601d00000020000000000801600800000020000000000000001d00000020000001600074001620000000001600000000000800000021600000000801600800001620000000000000000800000075600000000020000020000000000000000000000800000021600000000801600800001620000000000000001d00001620000001600075600020000000001600000000001d00000020000001600001600800000020000001600001601d00000074000001600020000000001600001600000001601d00000074000000000801600800001620000000001600001d00000074000001600074001620000000001600002400001d00000075600000000801600800001620000000000001600800000075600000000020000020000000000000000000000f00000020000000000801601d00000020000000000000001d00000020000001600020000020000000001600000000001d00001620000001600001601d00001620001600000001600800001674001600000021600000000000000000000000000f00000020000000000801601d00000020000000000000001d00000020000001600020000020000000001600000000000800000021600000000801600800001620000000000001601d00001675600001600020000020000000000000000000001d00000075600000000801600800001620000000000000001d00001620000001600075600020000000001600000000001d000000740000016000016008000016200000000000016008000016200000016000740000000016000000000016,
  0x1601d0010017410010010080160080010160013c100101600101d0010017410013d60017410160013c100101600102400101d00100175600100100801600800101600100100100101600800100100100100100100100100100100100100100100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100101d0010160010013d600101601d0010160010160010010160080010167410160010010160010010010010010013c101601d0010010010010010083d600800100100100100100100101d0010010010013d600174101600100100101600100100100800100101600100100801600800101600100100100100100800100175600100100100100100100100100100100100100800100101600100100801600800101600100100100100101d0010160010013d600175600100100100101600100100101d0010010010010160010160080010010010010160013d601d0010017410013d600100100100101600101600100101601d0010017410010010083d60080010160013c100101600101d0010017410013d60017410160013c100101600102400101d00100175600100100801600800101600100100100101600800100175600100100100100100100100100100100100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100101d0010160010013d600101601d0010160010160010010160080010167410160010010160010010010010010013c100100f0010010010010010083d601d0010010013c100100100101d00100100100101600100100100100100101600100100100800100101600100100801600800101600100100100101601d00101675600101600100100100100100100100100100101d00100175600100100801600800101600100100100100101d0010160010013d600175600100100100101600100100101d0010017410013d60010160080010160010010010013d60080010160010013d6001741001001016001001001016,
  0x1601d00000074000000000801600800001600000000001600001d00000074000001600074001600000000001600002400001d00000075600000000801600800001600000000000001600800000000000000000000000000000000000000000000000f00000000000000000801601d00000000000000000000001d00000000000001600000000000000000001600000000001d00001600000001600001601d00001600001600000001600800001674001600000001600000000000000000000001601d00000000000000000801600800000000000000000000001d00000000000001600074001600000000001600000000000800000001600000000801600800001600000000000000000800000075600000000000000000000000000000000000000800000001600000000801600800001600000000000000001d00001600000001600075600000000000001600000000001d00000000000001600001600800000000000001600001601d00000074000001600000000000001600001600000001601d00000074000000000801600800001600000000001600001d00000074000001600074001600000000001600002400001d00000075600000000801600800001600000000000001600800000075600000000000000000000000000000000000000f00000000000000000801601d00000000000000000000001d00000000000001600000000000000000001600000000001d00001600000001600001601d00001600001600000001600800001674001600000001600000000000000000000000000f00000000000000000801601d00000000000000000000001d00000000000001600000000000000000001600000000000800000001600000000801600800001600000000000001601d00001675600001600000000000000000000000000000001d00000075600000000801600800001600000000000000001d00001600000001600075600000000000001600000000001d000000740000016000016008000016000000000000016008000016000000016000740000000016000000000016,
  0x55554001c1c000054054070001501501c00701c0005470005400000071c00005400151d500055500700701c01501c5400005400231c001554000070001501500700700700054702301500001c0070005405401c000000000754700700001c00000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354054000001c1c000054001570001500001c00701c55554702301501501c0070005550001c001554001c00700e54000700001554001c1c000054054070000054001c00700700000700054000001c1c00005400001c000001500701c00701501c54000000000e1c00005400001c001501500700700700054700000000001c0070005405401c000054001c54700700001c00000000000e1c001500000070001501501c00700700054700054000001c1c00005400151c000054001c54701c0150235405400000071c00000000151c001500001c00700754054700001554001c0070005400001d554054000700701c55554700055554001c1c000054054070001555501c00701c00054700054000001c1c00005400151d500055500701c01c01501c5400005400231c001554000070001501500700700700054702301500001c0070005405401c000054001c54700700001c00000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354054000001c1c000054001570001500001c00701c55554702301501501c0070005550001c001554001c00700e54000700000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354000000000e1c001554000070001501501c00700700054700001500001c00700054055570000054001c54701c54001c0000005400231c00155400007000150150070070070005470235400000071c000054001570000054000700701c55502354054000001c1c00005400151d501501501c00700700054702301555501c00700054001570000054001c00701c54055c555,
  0x1c00000000000070000000001c00001c00000000000038000000e00000000000000000000000001c00001c00038000002300000000000070000000000000000000000002300000001c00000e00000000000000000000000000001c00000000001c00000000000000000000001c00000000e00000000000000000e00000000000000e00000000001c00002300000038001c00e00000000070000000001c00001c0000003a300000001c00000000000000000000001c00000e00000000000000001c00000000000070000000001c00000000000000000038001c00000000000000000000000001c00000001c00038000000e00000000000000000000000000000000000000e00000001c00000000000000000000001c00000000039c00000000000e00000000000070000000001c00000000000000e00038001c00000000000000000e00001c00001c00002300000000000000e00000000000000000001c00000000000038e00000001c00000000000000000000000000001c00000000000000001c00000000000070000000001c00001c00000000000038001c00e00000000000000000000001c01c00001c00038000002300000000000070000000000000000000000002300000001c00000e00000000000000001c00000000039c00000000001c00000000000000000000001c00000000e00000000000000000e00000000000000e00000000001c00002300000038001c00e00000000070000000001c00001c0000003a300000001c00000000000000000000001c00000e00000000000000001c00000000000000000000001c00000000e00000000000000000e00000000000000e00000000001c00002300038000000e00000000000070000000001c00000000000000e00000001c00000e00000070000000001c00001c00039c00038000002300000000000070000000000000000000000002300038000000e00000000070000e00000000001c00002300000038001c00e00000000000000000001c00000000000002300000001c00000000000070000000001c00001c00001c000,
  0x55554001c1c000054054070001501501c00701c0005470005400000071c00005400151d500055500700701c01501c5400005400231c001554000070001501500700700700054702301500001c0070005405401c000000000754700700001c00000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354054000001c1c000054001570001500001c00701c55554702301501501c0070005550001c001554001c00700e54000700001554001c1c000054054070000054001c00700700000700054000001c1c00005400001c000001500701c00701501c54000000000e1c00005400001c001501500700700700054700000000001c0070005405401c000054001c54700700001c00000000000e1c001500000070001501501c00700700054700054000001c1c00005400151c000054001c54701c0150235405400000071c00000000151c001500001c00700754054700001554001c0070005400001d554054000700701c55554700055554001c1c000054054070001555501c00701c00054700054000001c1c00005400151d500055500701c01c01501c5400005400231c001554000070001501500700700700054702301500001c0070005405401c000054001c54700700001c00000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354054000001c1c000054001570001500001c00701c55554702301501501c0070005550001c001554001c00700e54000700000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354000000000e1c001554000070001501501c00700700054700001500001c00700054055570000054001c54701c54001c0000005400231c00155400007000150150070070070005470235400000071c000054001570000054000700701c55502354054000001c1c00005400151d501501501c00700700054702301555501c00700054001570000054001c00701c54055c555,
  0x1c1c000000000070000000001c00701c0000070000000000071c00000000001c000000000700701c00001c0000000000231c000000000070000000000700700700000702300000001c0070000000001c000000000700700700001c00000000001c1c00000000001c000000001c0070070000070000000000071c00000000001c000000000700701c00002300000000001c1c000000000070000000001c00701c00000702300000001c0070000000001c000000001c00700e00000700000000001c1c000000000070000000001c00700700000700000000001c1c00000000001c000000000701c00700001c00000000000e1c00000000001c000000000700700700000700000000001c0070000000001c000000001c00700700001c00000000000e1c000000000070000000001c00700700000700000000001c1c00000000001c000000001c00701c0000230000000000071c00000000001c000000001c00700700000700000000001c0070000000001c000000000700701c00000700000000001c1c000000000070000000001c00701c00000700000000001c1c00000000001c000000000701c01c00001c0000000000231c000000000070000000000700700700000702300000001c0070000000001c000000001c00700700001c00000000001c1c00000000001c000000001c0070070000070000000000071c00000000001c000000000700701c00002300000000001c1c000000000070000000001c00701c00000702300000001c0070000000001c000000001c00700e00000700000000001c1c00000000001c000000001c0070070000070000000000071c00000000001c000000000700701c00002300000000000e1c000000000070000000001c00700700000700000000001c00700000000070000000001c00701c00001c0000000000231c00000000007000000000070070070000070230000000071c000000000070000000000700701c00002300000000001c1c00000000001c000000001c00700700000702300000001c00700000000070000000001c00701c00001c000,
  0x55554001c1c000054054070001501501c00701c0005470005400000071c00005400151d500055500700701c01501c5400005400231c001554000070001501500700700700054702301500001c0070005405401c000000000754700700001c00000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354054000001c1c000054001570001500001c00701c55554702301501501c0070005550001c001554001c00700e54000700001554001c1c000054054070000054001c00700700000700054000001c1c00005400001c000001500701c00701501c54000000000e1c00005400001c001501500700700700054700000000001c0070005405401c000054001c54700700001c00000000000e1c001500000070001501501c00700700054700054000001c1c00005400151c000054001c54701c0150235405400000071c00000000151c001500001c00700754054700001554001c0070005400001d554054000700701c55554700055554001c1c000054054070001555501c00701c00054700054000001c1c00005400151d500055500701c01c01501c5400005400231c001554000070001501500700700700054702301500001c0070005405401c000054001c54700700001c00000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354054000001c1c000054001570001500001c00701c55554702301501501c0070005550001c001554001c00700e54000700000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354000000000e1c001554000070001501501c00700700054700001500001c00700054055570000054001c54701c54001c0000005400231c00155400007000150150070070070005470235400000071c000054001570000054000700701c55502354054000001c1c00005400151d501501501c00700700054702301555501c00700054001570000054001c00701c54055c555,
  0x1c00000000000070000000001c00001c00000000000038000000e00000000000000000000000001c00001c00038000002300000000000070000000000000000000000002300000001c00000e00000000000000000000000000001c00000000001c00000000000000000000001c00000000e00000000000000000e00000000000000e00000000001c00002300000038001c00e00000000070000000001c00001c0000003a300000001c00000000000000000000001c00000e00000000000000001c00000000000070000000001c00000000000000000038001c00000000000000000000000001c00000001c00038000000e00000000000000000000000000000000000000e00000001c00000000000000000000001c00000000039c00000000000e00000000000070000000001c00000000000000e00038001c00000000000000000e00001c00001c00002300000000000000e00000000000000000001c00000000000038e00000001c00000000000000000000000000001c00000000000000001c00000000000070000000001c00001c00000000000038001c00e00000000000000000000001c01c00001c00038000002300000000000070000000000000000000000002300000001c00000e00000000000000001c00000000039c00000000001c00000000000000000000001c00000000e00000000000000000e00000000000000e00000000001c00002300000038001c00e00000000070000000001c00001c0000003a300000001c00000000000000000000001c00000e00000000000000001c00000000000000000000001c00000000e00000000000000000e00000000000000e00000000001c00002300038000000e00000000000070000000001c00000000000000e00000001c00000e00000070000000001c00001c00039c00038000002300000000000070000000000000000000000002300038000000e00000000070000e00000000001c00002300000038001c00e00000000000000000001c00000000000002300000001c00000000000070000000001c00001c00001c000,
  0x55554001c1c000054054070001501501c00701c0005470005400000071c00005400151d500055500700701c01501c5400005400231c001554000070001501500700700700054702301500001c0070005405401c000000000754700700001c00000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354054000001c1c000054001570001500001c00701c55554702301501501c0070005550001c001554001c00700e54000700001554001c1c000054054070000054001c00700700000700054000001c1c00005400001c000001500701c00701501c54000000000e1c00005400001c001501500700700700054700000000001c0070005405401c000054001c54700700001c00000000000e1c001500000070001501501c00700700054700054000001c1c00005400151c000054001c54701c0150235405400000071c00000000151c001500001c00700754054700001554001c0070005400001d554054000700701c55554700055554001c1c000054054070001555501c00701c00054700054000001c1c00005400151d500055500701c01c01501c5400005400231c001554000070001501500700700700054702301500001c0070005405401c000054001c54700700001c00000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354054000001c1c000054001570001500001c00701c55554702301501501c0070005550001c001554001c00700e54000700000054001c1c05405400001c001554001c0070070005470005400000071c00000000151c000054000700701c55502354000000000e1c001554000070001501501c00700700054700001500001c00700054055570000054001c54701c54001c0000005400231c00155400007000150150070070070005470235400000071c000054001570000054000700701c55502354054000001c1c00005400151d501501501c00700700054702301555501c00700054001570000054001c00701c54055c555,
  0x1c00000000000070000000001c00001c00000000000000000000000000000000000000000000001c00001c00000000002300000000000070000000000000000000000002300000001c00000000000000000000000000000000001c00000000001c00000000000000000000001c00000000000000000000000000000000000000000000000000001c00002300000000001c00000000000070000000001c00001c00000002300000001c00000000000000000000001c00000e00000000000000001c00000000000070000000001c00000000000000000000001c00000000000000000000000001c00000001c00000000000e00000000000000000000000000000000000000000000001c00000000000000000000001c00000000001c00000000000e00000000000070000000001c00000000000000000000001c00000000000000000000001c00001c00002300000000000000000000000000000000001c00000000000000000000001c00000000000000000000000000001c00000000000000001c00000000000070000000001c00001c00000000000000001c00000000000000000000000001c01c00001c00000000002300000000000070000000000000000000000002300000001c00000000000000000000001c00000000001c00000000001c00000000000000000000001c00000000000000000000000000000000000000000000000000001c00002300000000001c00000000000070000000001c00001c00000002300000001c00000000000000000000001c00000e00000000000000001c00000000000000000000001c00000000000000000000000000000000000000000000000000001c00002300000000000e00000000000070000000001c00000000000000000000001c00000000000070000000001c00001c00001c00000000002300000000000070000000000000000000000002300000000000000000000070000000000000001c00002300000000001c00000000000000000000001c00000000000002300000001c00000000000070000000001c00001c00001c000,
  0x5145066c00001805000000220140066c00008800005000005000061800001805000000001805006d40001800000005000000061800001945000000000140066c00006d40005000000140066c00001800005000001800003400001800000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c00140005000000061800141805000000000140066c00006c05145000000140061800001805000005001945006c00001805000000000145061800001805000000220005066c00003400000000005000066c00001805000000001800001940006c00000005000000061800001805000000000140061800006d400050000000000618000018050000000018050034000018000000000000001b1800001940000000220140061800006d40005000000000061800001805000000001805006c00006c00000005005000061800001800000000000140066c00001805000000000145066c00001805000000001805006c00001805005140005145066c00001805000000220145066c00008800005000005000066c00001805000000001805006d40006c00000005000000061800001945000000000140066c00006d40005000000140066c00001805005000001805003400001800000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c00140005000000061800141805000000000140066c00006c05145000000140061800001805000005001945006c00001805000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c001400050000001b1800001945000000220140061800006d40005000000140066c00001805005000001805008800001805000000000000061800001945000000000140066c00006d40005000005000061800141805000000001805001800006c00140005005000066c00001805000000000140066c00006d40005000000145066c00001805000000001805006c00006c0500500514,
  0x6c00000000003400220000006c00008800000000000000000000000000000000000000006c000000034000000000000000000000000000000d0000006c00006c00000000000000006c000000000d00000000000034000000000000000000000000000000000034000d0000006c000088000000000000000000000000000000000000000d0000006c000000000000d0000000000000000000000000006c00006c00000000000000000000000000000000000000006c00000000000000000000000000000000000000220000006c00003400000000000000006c000000000000000000000d0000006c034000000000000000000000000000000d0000000000006c000000000000000000000000000000000000000034000000000000034000001b0000000000000000220000000000006c000000000000d0000000000000000000000000006c00006c03400000000000000000000000000000000000006c00000000000000000000006c00000000000000000000006c000000000d0000000000006c00000000003400220000006c00008800000000000000006c000000000000000000000d6c00006c034000000000000000000000000000000d0000006c00006c00000000000000006c000000000d00000000000034000000000000034000000000000000000034000d0000006c000088000000000000000000000000000000000000000d0000006c000000000000d0000000000000000000000000006c00006c00000000000000000000000000000000000000006c000000000000000000000000000000000034000d0000006c000088000000000000000000000000000000000000000d0000006c000000000000001b0000000000000000220000000000006c00000000000000006c000000000000000000000088000000000000034000000000000000000000000d0000006c00006c000000000000d00000000000000000000000000d0000006c03400000000000006c00000000000000000000006c00006c00000000000000006c00000000000000000000006c00006c000d000000,
  0x5145066c00001805000000220140066c00008800005000005000061800001805000000001805006d40001800000005000000061800001945000000000140066c00006d40005000000140066c00001800005000001800003400001800000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c00140005000000061800141805000000000140066c00006c05145000000140061800001805000005001945006c00001805000000000145061800001805000000220005066c00003400000000005000066c00001805000000001800001940006c00000005000000061800001805000000000140061800006d400050000000000618000018050000000018050034000018000000000000001b1800001940000000220140061800006d40005000000000061800001805000000001805006c00006c00000005005000061800001800000000000140066c00001805000000000145066c00001805000000001805006c00001805005140005145066c00001805000000220145066c00008800005000005000066c00001805000000001805006d40006c00000005000000061800001945000000000140066c00006d40005000000140066c00001805005000001805003400001800000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c00140005000000061800141805000000000140066c00006c05145000000140061800001805000005001945006c00001805000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c001400050000001b1800001945000000220140061800006d40005000000140066c00001805005000001805008800001805000000000000061800001945000000000140066c00006d40005000005000061800141805000000001805001800006c00140005005000066c00001805000000000140066c00006d40005000000145066c00001805000000001805006c00006c0500500514,
  0x66c00001800000000220000066c00008800000000000000061800001800000000001800006c00001800000000000000061800001800000000000000066c00006c00000000000000066c00001800000000001800003400001800000000000000061800001800000000000000066c00008800000000000000061800001800000000001800001800006c00000000000000061800001800000000000000066c00006c00000000000000061800001800000000001800006c00001800000000000000061800001800000000220000066c00003400000000000000066c00001800000000001800001800006c00000000000000061800001800000000000000061800006c000000000000000618000018000000000018000034000018000000000000001b1800001800000000220000061800006c00000000000000061800001800000000001800006c00006c00000000000000061800001800000000000000066c00001800000000000000066c00001800000000001800006c00001800000000000000066c00001800000000220000066c00008800000000000000066c00001800000000001800006c00006c00000000000000061800001800000000000000066c00006c00000000000000066c00001800000000001800003400001800000000000000061800001800000000000000066c00008800000000000000061800001800000000001800001800006c00000000000000061800001800000000000000066c00006c00000000000000061800001800000000001800006c00001800000000000000061800001800000000000000066c00008800000000000000061800001800000000001800001800006c000000000000001b1800001800000000220000061800006c00000000000000066c00001800000000001800008800001800000000000000061800001800000000000000066c00006c00000000000000061800001800000000001800001800006c00000000000000066c00001800000000000000066c00006c00000000000000066c00001800000000001800006c00006c0000000000,
  0x5145066c00001805000000220140066c00008800005000005000061800001805000000001805006d40001800000005000000061800001945000000000140066c00006d40005000000140066c00001800005000001800003400001800000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c00140005000000061800141805000000000140066c00006c05145000000140061800001805000005001945006c00001805000000000145061800001805000000220005066c00003400000000005000066c00001805000000001800001940006c00000005000000061800001805000000000140061800006d400050000000000618000018050000000018050034000018000000000000001b1800001940000000220140061800006d40005000000000061800001805000000001805006c00006c00000005005000061800001800000000000140066c00001805000000000145066c00001805000000001805006c00001805005140005145066c00001805000000220145066c00008800005000005000066c00001805000000001805006d40006c00000005000000061800001945000000000140066c00006d40005000000140066c00001805005000001805003400001800000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c00140005000000061800141805000000000140066c00006c05145000000140061800001805000005001945006c00001805000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c001400050000001b1800001945000000220140061800006d40005000000140066c00001805005000001805008800001805000000000000061800001945000000000140066c00006d40005000005000061800141805000000001805001800006c00140005005000066c00001805000000000140066c00006d40005000000145066c00001805000000001805006c00006c0500500514,
  0x6c00000000003400220000006c00008800000000000000000000000000000000000000006c000000034000000000000000000000000000000d0000006c00006c00000000000000006c000000000d00000000000034000000000000000000000000000000000034000d0000006c000088000000000000000000000000000000000000000d0000006c000000000000d0000000000000000000000000006c00006c00000000000000000000000000000000000000006c00000000000000000000000000000000000000220000006c00003400000000000000006c000000000000000000000d0000006c034000000000000000000000000000000d0000000000006c000000000000000000000000000000000000000034000000000000034000001b0000000000000000220000000000006c000000000000d0000000000000000000000000006c00006c03400000000000000000000000000000000000006c00000000000000000000006c00000000000000000000006c000000000d0000000000006c00000000003400220000006c00008800000000000000006c000000000000000000000d6c00006c034000000000000000000000000000000d0000006c00006c00000000000000006c000000000d00000000000034000000000000034000000000000000000034000d0000006c000088000000000000000000000000000000000000000d0000006c000000000000d0000000000000000000000000006c00006c00000000000000000000000000000000000000006c000000000000000000000000000000000034000d0000006c000088000000000000000000000000000000000000000d0000006c000000000000001b0000000000000000220000000000006c00000000000000006c000000000000000000000088000000000000034000000000000000000000000d0000006c00006c000000000000d00000000000000000000000000d0000006c03400000000000006c00000000000000000000006c00006c00000000000000006c00000000000000000000006c00006c000d000000,
  0x5145066c00001805000000220140066c00008800005000005000061800001805000000001805006d40001800000005000000061800001945000000000140066c00006d40005000000140066c00001800005000001800003400001800000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c00140005000000061800141805000000000140066c00006c05145000000140061800001805000005001945006c00001805000000000145061800001805000000220005066c00003400000000005000066c00001805000000001800001940006c00000005000000061800001805000000000140061800006d400050000000000618000018050000000018050034000018000000000000001b1800001940000000220140061800006d40005000000000061800001805000000001805006c00006c00000005005000061800001800000000000140066c00001805000000000145066c00001805000000001805006c00001805005140005145066c00001805000000220145066c00008800005000005000066c00001805000000001805006d40006c00000005000000061800001945000000000140066c00006d40005000000140066c00001805005000001805003400001800000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c00140005000000061800141805000000000140066c00006c05145000000140061800001805000005001945006c00001805000000000005061800001805000000000145066c00008800005000005000061800001800000000001800001800006c001400050000001b1800001945000000220140061800006d40005000000140066c00001805005000001805008800001805000000000000061800001945000000000140066c00006d40005000005000061800141805000000001805001800006c00140005005000066c00001805000000000140066c00006d40005000000145066c00001805000000001805006c00006c0500500514,
  0x6c00000000000000220000006c00008800000000000000000000000000000000000000006c00000000000000000000000000000000000000000000006c00006c00000000000000006c00000000000000000000003400000000000000000000000000000000000000000000006c00008800000000000000000000000000000000000000000000006c00000000000000000000000000000000000000006c00006c00000000000000000000000000000000000000006c00000000000000000000000000000000000000220000006c00003400000000000000006c00000000000000000000000000006c00000000000000000000000000000000000000000000006c000000000000000000000000000000000000000034000000000000000000001b0000000000000000220000000000006c00000000000000000000000000000000000000006c00006c00000000000000000000000000000000000000006c00000000000000000000006c00000000000000000000006c00000000000000000000006c00000000000000220000006c00008800000000000000006c00000000000000000000006c00006c00000000000000000000000000000000000000006c00006c00000000000000006c00000000000000000000003400000000000000000000000000000000000000000000006c00008800000000000000000000000000000000000000000000006c00000000000000000000000000000000000000006c00006c00000000000000000000000000000000000000006c00000000000000000000000000000000000000000000006c00008800000000000000000000000000000000000000000000006c000000000000001b0000000000000000220000000000006c00000000000000006c00000000000000000000008800000000000000000000000000000000000000000000006c00006c00000000000000000000000000000000000000000000006c00000000000000006c00000000000000000000006c00006c00000000000000006c00000000000000000000006c00006c0000000000,
  0x134c00056800004c001a1400000000056800050004c500000000001a8400004c000c1400004c00051400050000050000000004c56800004c001a1400000000051400050004c50000130000056a10000004c514000000000514001a0000050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000000058400004c00051400130000056800054c04da0000000000056800004c00051400004c00051614c54c00050000130000051400004c001a1400000000051610050000050000000000053000004c000c1400000130051400050000050000000004c56800004c00051400000000051400050004c50000000000056800004c00051400004c00051400050000050000000004c51400000000051400000000056800050004c50000000000053000004c00051400004c00056930050000054d300000001a3000000000051400130000056a10054c00050000130000056a10004c000c1400000000051400054d34c50130134c00056800004c001a1400000000056a10050004c500000000001a8400004c000c1400004d30051400050000050000000004c56800004c001a1400000000051400050004c50000130000056a10004c04c51400004c000514001a0000050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000000058400004c00051400130000056800054c04da0000000000056800004c00051400004c00051614c54c00050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000004c56800004c00051400000000056800050004c50000130000056800004c04da1400004c00051400050000050000000004c56800004c001a1400000000051400050004c500000000001a8400004c00051400004c000514000500001a4c000000001a8400004c000c1400000000056800050004c50000000000056a10004c00051400004c00056a10054c04c54c0,
  0x68000000001a00000030000068c00000000000000000001a84000000000c00000000000000000000030000000000000068000000001a00000030000000c0000000000000000000006a100000000000000000000000001a00000000000000000000000c0000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000084000000000000000000000068c00000001a00000030000068c00000000000000c00000002100000000000000000000000000000001a00000030000002100000000000000000000030000000000c00000000000000000000030000000000000068000000000000000030000000c00000000000000000000068c00000000000000000000000000000000000000000000000000c00000000000030000068c00000000000000000000030000000000000000000000068000000000000000000001a3000000000000000000000006a10000000000000000000006a100000000c00000c00000000c00000000000000000000068000000001a0000003000006a100000000000000000001a84000000000c00000000000000000000030000000000000068000000001a00000030000000c0000000000000000000006a100000000000000000000000001a00000000000000000000000c0000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000084000000000000000000000068c00000001a00000030000068c00000000000000c00000002100000000000000000000000000c0000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000068000c00000000000030000068c00000000000000000000068c00000001a00000000000000000000000000000000000068000000001a00000030000000c00000000000000000001a84000000000000000000000000000000001a00000000001a84000000000c00000030000068c0000000000000003000006a10000000000000000000006a1000000000000,
  0x134c00056800004c001a1400000000056800050004c500000000001a8400004c000c1400004c00051400050000050000000004c56800004c001a1400000000051400050004c50000130000056a10000004c514000000000514001a0000050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000000058400004c00051400130000056800054c04da0000000000056800004c00051400004c00051614c54c00050000130000051400004c001a1400000000051610050000050000000000053000004c000c1400000130051400050000050000000004c56800004c00051400000000051400050004c50000000000056800004c00051400004c00051400050000050000000004c51400000000051400000000056800050004c50000000000053000004c00051400004c00056930050000054d300000001a3000000000051400130000056a10054c00050000130000056a10004c000c1400000000051400054d34c50130134c00056800004c001a1400000000056a10050004c500000000001a8400004c000c1400004d30051400050000050000000004c56800004c001a1400000000051400050004c50000130000056a10004c04c51400004c000514001a0000050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000000058400004c00051400130000056800054c04da0000000000056800004c00051400004c00051614c54c00050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000004c56800004c00051400000000056800050004c50000130000056800004c04da1400004c00051400050000050000000004c56800004c001a1400000000051400050004c500000000001a8400004c00051400004c000514000500001a4c000000001a8400004c000c1400000000056800050004c50000000000056a10004c00051400004c00056a10054c04c54c0,
  0x568000000001a14000000000568000500000500000000001a84000000000c14000000000514000500000500000000000568000000001a1400000000051400050000050000000000056a100000000514000000000514001a0000050000000000051400000000051400000000056a100500001a00000000001a30000000000514000000000514000500001a00000000000584000000000514000000000568000500001a00000000000568000000000514000000000516100500000500000000000514000000001a14000000000516100500000500000000000530000000000c14000000000514000500000500000000000568000000000514000000000514000500000500000000000568000000000514000000000514000500000500000000000514000000000514000000000568000500000500000000000530000000000514000000000568000500000500000000001a3000000000051400000000056a10050000050000000000056a100000000c14000000000514000500000500000000000568000000001a1400000000056a100500000500000000001a84000000000c14000000000514000500000500000000000568000000001a1400000000051400050000050000000000056a100000000514000000000514001a0000050000000000051400000000051400000000056a100500001a00000000001a30000000000514000000000514000500001a00000000000584000000000514000000000568000500001a0000000000056800000000051400000000051610050000050000000000051400000000051400000000056a100500001a00000000001a30000000000514000000000514000500001a00000000000568000000000514000000000568000500000500000000000568000000001a14000000000514000500000500000000000568000000001a14000000000514000500000500000000001a84000000000514000000000514000500001a00000000001a84000000000c1400000000056800050000050000000000056a10000000051400000000056a1005000005000,
  0x134c00056800004c001a1400000000056800050004c500000000001a8400004c000c1400004c00051400050000050000000004c56800004c001a1400000000051400050004c50000130000056a10000004c514000000000514001a0000050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000000058400004c00051400130000056800054c04da0000000000056800004c00051400004c00051614c54c00050000130000051400004c001a1400000000051610050000050000000000053000004c000c1400000130051400050000050000000004c56800004c00051400000000051400050004c50000000000056800004c00051400004c00051400050000050000000004c51400000000051400000000056800050004c50000000000053000004c00051400004c00056930050000054d300000001a3000000000051400130000056a10054c00050000130000056a10004c000c1400000000051400054d34c50130134c00056800004c001a1400000000056a10050004c500000000001a8400004c000c1400004d30051400050000050000000004c56800004c001a1400000000051400050004c50000130000056a10004c04c51400004c000514001a0000050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000000058400004c00051400130000056800054c04da0000000000056800004c00051400004c00051614c54c00050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000004c56800004c00051400000000056800050004c50000130000056800004c04da1400004c00051400050000050000000004c56800004c001a1400000000051400050004c500000000001a8400004c00051400004c000514000500001a4c000000001a8400004c000c1400000000056800050004c50000000000056a10004c00051400004c00056a10054c04c54c0,
  0x68000000001a00000030000068c00000000000000000001a84000000000c00000000000000000000030000000000000068000000001a00000030000000c0000000000000000000006a100000000000000000000000001a00000000000000000000000c0000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000084000000000000000000000068c00000001a00000030000068c00000000000000c00000002100000000000000000000000000000001a00000030000002100000000000000000000030000000000c00000000000000000000030000000000000068000000000000000030000000c00000000000000000000068c00000000000000000000000000000000000000000000000000c00000000000030000068c00000000000000000000030000000000000000000000068000000000000000000001a3000000000000000000000006a10000000000000000000006a100000000c00000c00000000c00000000000000000000068000000001a0000003000006a100000000000000000001a84000000000c00000000000000000000030000000000000068000000001a00000030000000c0000000000000000000006a100000000000000000000000001a00000000000000000000000c0000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000084000000000000000000000068c00000001a00000030000068c00000000000000c00000002100000000000000000000000000c0000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000068000c00000000000030000068c00000000000000000000068c00000001a00000000000000000000000000000000000068000000001a00000030000000c00000000000000000001a84000000000000000000000000000000001a00000000001a84000000000c00000030000068c0000000000000003000006a10000000000000000000006a1000000000000,
  0x134c00056800004c001a1400000000056800050004c500000000001a8400004c000c1400004c00051400050000050000000004c56800004c001a1400000000051400050004c50000130000056a10000004c514000000000514001a0000050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000000058400004c00051400130000056800054c04da0000000000056800004c00051400004c00051614c54c00050000130000051400004c001a1400000000051610050000050000000000053000004c000c1400000130051400050000050000000004c56800004c00051400000000051400050004c50000000000056800004c00051400004c00051400050000050000000004c51400000000051400000000056800050004c50000000000053000004c00051400004c00056930050000054d300000001a3000000000051400130000056a10054c00050000130000056a10004c000c1400000000051400054d34c50130134c00056800004c001a1400000000056a10050004c500000000001a8400004c000c1400004d30051400050000050000000004c56800004c001a1400000000051400050004c50000130000056a10004c04c51400004c000514001a0000050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000000058400004c00051400130000056800054c04da0000000000056800004c00051400004c00051614c54c00050000004c00051400000000051400130000056a10050004da00000000001a30000000000514000000000514000500001a4c00000004c56800004c00051400000000056800050004c50000130000056800004c04da1400004c00051400050000050000000004c56800004c001a1400000000051400050004c500000000001a8400004c00051400004c000514000500001a4c000000001a8400004c000c1400000000056800050004c50000000000056a10004c00051400004c00056a10054c04c54c0,
  0x68000000001a00000000000068000000000000000000001a84000000000c00000000000000000000000000000000000068000000001a0000000000000000000000000000000000006a100000000000000000000000001a0000000000000000000000000000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000084000000000000000000000068000000001a00000000000068000000000000000000000002100000000000000000000000000000001a00000000000002100000000000000000000030000000000c00000000000000000000000000000000000068000000000000000000000000000000000000000000000068000000000000000000000000000000000000000000000000000000000000000000000068000000000000000000000030000000000000000000000068000000000000000000001a3000000000000000000000006a10000000000000000000006a100000000c00000000000000000000000000000000000068000000001a0000000000006a100000000000000000001a84000000000c00000000000000000000000000000000000068000000001a0000000000000000000000000000000000006a100000000000000000000000001a0000000000000000000000000000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000084000000000000000000000068000000001a0000000000006800000000000000000000000210000000000000000000000000000000000000000000006a100000001a00000000001a30000000000000000000000000000000001a00000000000068000000000000000000000068000000000000000000000068000000001a00000000000000000000000000000000000068000000001a00000000000000000000000000000000001a84000000000000000000000000000000001a00000000001a84000000000c0000000000006800000000000000000000006a10000000000000000000006a1000000000000,
  0x6404921000001004800000006400001000001000004800121000001000001004800120002c00001000001000000000001000001000001004800000006400001000001000000000001000201000002c00000000001000001004801000000000001004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120002c00001000006404800120006400201000001000004800001000001000002c00000000001124801000001004800000121000001000006404800000006400001000001000000000001000001000001004800000008000001000001000000000001000001000001004800000001000001000001000000000001000001000008004800000006404801004801000000000001000001000001120000000001000001000001000000000002c00001000006404800120002c04801000001000000000001000001000001000000120001000201000006400000000006400201000001004800000001000001000001000004800006404921000006404800000006400001000001000004800121000001000001004800120008000001000001000000000001000001000001004800000006400001000001000000000001000201000008004800000006404801004801000000000001004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120002c00001000006404800120006400201000001000004800001000001000002c00000000001124801000001004800000121004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120001000001000001124800000001000001000001000000000006400201000008004800000006404801004801000000000001000001000001004800000006400001000001000000000002c0000100000640480012000800480640000100000012000100000100000100480012000640000100000100000000000640000100000640480012000640480100000100480480000,
  0x64000000000000000000000064000b0000000000000000000000000000000000000000002c000000000000000000000000000000000000000000000064000b0000000002c00000000000200000002c00002c00000000000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c00006400000000000000002c000000000064000000000064002000000000000000000000000b0000002c00002c000000000000000000000000000000000000000064000000000064000b00000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000b0000000002c000000000000b00000080000000000064000000000000000000000000000000000000000000000000000b0000000002c00000002c00000000006400000000002c00000000000000000000000000000000000000000000000000200000006402c000000064002000000000000000000000000000000000000000000064000000000064000000000064000b00000000000000000000000000000000000000000080000000000000000000000000000000000000000000000064000b0000000002c00000000000200000008000002c00006400000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c00006400000000000000002c000000000064000000000064002000000000000000000000000b0000002c00002c00000000000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c000064000000000000000000000000000000000000000000000b0000000002c000000064002000000080000000000064000000000000000000000000000000000000000000000064000b0000000002c00000002c000000000064000000000080000064000000000000000000000000000000000000000064000b0000000002c000000064000b000000640000000000640000000000000000000000,
  0x6404921000001004800000006400001000001000004800121000001000001004800120002c00001000001000000000001000001000001004800000006400001000001000000000001000201000002c00000000001000001004801000000000001004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120002c00001000006404800120006400201000001000004800001000001000002c00000000001124801000001004800000121000001000006404800000006400001000001000000000001000001000001004800000008000001000001000000000001000001000001004800000001000001000001000000000001000001000008004800000006404801004801000000000001000001000001120000000001000001000001000000000002c00001000006404800120002c04801000001000000000001000001000001000000120001000201000006400000000006400201000001004800000001000001000001000004800006404921000006404800000006400001000001000004800121000001000001004800120008000001000001000000000001000001000001004800000006400001000001000000000001000201000008004800000006404801004801000000000001004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120002c00001000006404800120006400201000001000004800001000001000002c00000000001124801000001004800000121004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120001000001000001124800000001000001000001000000000006400201000008004800000006404801004801000000000001000001000001004800000006400001000001000000000002c0000100000640480012000800480640000100000012000100000100000100480012000640000100000100000000000640000100000640480012000640480100000100480480000,
  0x6400001000001000000000006400001000001000000000001000001000001000000000002c00001000001000000000001000001000001000000000006400001000001000000000001000201000002c00000000001000001000001000000000001000001000001000000000006400201000006400000000001000001000001000000000002c00006400001000000000002c00001000006400000000006400201000001000000000001000001000002c00000000001000001000001000000000001000001000006400000000006400001000001000000000001000001000001000000000008000001000001000000000001000001000001000000000001000001000001000000000001000001000008000000000006400001000001000000000001000001000001000000000001000001000001000000000002c00001000006400000000002c00001000001000000000001000001000001000000000001000201000006400000000006400201000001000000000001000001000001000000000006400001000006400000000006400001000001000000000001000001000001000000000008000001000001000000000001000001000001000000000006400001000001000000000001000201000008000000000006400001000001000000000001000001000001000000000006400201000006400000000001000001000001000000000002c00006400001000000000002c00001000006400000000006400201000001000000000001000001000002c00000000001000001000001000000000001000001000001000000000006400201000006400000000001000001000001000000000002c00006400001000000000001000001000001000000000001000001000001000000000006400201000008000000000006400001000001000000000001000001000001000000000006400001000001000000000002c0000100000640000000000800000640000100000000000100000100000100000000000640000100000100000000000640000100000640000000000640000100000100000000000,
  0x6404921000001004800000006400001000001000004800121000001000001004800120002c00001000001000000000001000001000001004800000006400001000001000000000001000201000002c00000000001000001004801000000000001004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120002c00001000006404800120006400201000001000004800001000001000002c00000000001124801000001004800000121000001000006404800000006400001000001000000000001000001000001004800000008000001000001000000000001000001000001004800000001000001000001000000000001000001000008004800000006404801004801000000000001000001000001120000000001000001000001000000000002c00001000006404800120002c04801000001000000000001000001000001000000120001000201000006400000000006400201000001004800000001000001000001000004800006404921000006404800000006400001000001000004800121000001000001004800120008000001000001000000000001000001000001004800000006400001000001000000000001000201000008004800000006404801004801000000000001004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120002c00001000006404800120006400201000001000004800001000001000002c00000000001124801000001004800000121004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120001000001000001124800000001000001000001000000000006400201000008004800000006404801004801000000000001000001000001004800000006400001000001000000000002c0000100000640480012000800480640000100000012000100000100000100480012000640000100000100000000000640000100000640480012000640480100000100480480000,
  0x64000000000000000000000064000b0000000000000000000000000000000000000000002c000000000000000000000000000000000000000000000064000b0000000002c00000000000200000002c00002c00000000000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c00006400000000000000002c000000000064000000000064002000000000000000000000000b0000002c00002c000000000000000000000000000000000000000064000000000064000b00000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000b0000000002c000000000000b00000080000000000064000000000000000000000000000000000000000000000000000b0000000002c00000002c00000000006400000000002c00000000000000000000000000000000000000000000000000200000006402c000000064002000000000000000000000000000000000000000000064000000000064000000000064000b00000000000000000000000000000000000000000080000000000000000000000000000000000000000000000064000b0000000002c00000000000200000008000002c00006400000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c00006400000000000000002c000000000064000000000064002000000000000000000000000b0000002c00002c00000000000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c000064000000000000000000000000000000000000000000000b0000000002c000000064002000000080000000000064000000000000000000000000000000000000000000000064000b0000000002c00000002c000000000064000000000080000064000000000000000000000000000000000000000064000b0000000002c000000064000b000000640000000000640000000000000000000000,
  0x6404921000001004800000006400001000001000004800121000001000001004800120002c00001000001000000000001000001000001004800000006400001000001000000000001000201000002c00000000001000001004801000000000001004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120002c00001000006404800120006400201000001000004800001000001000002c00000000001124801000001004800000121000001000006404800000006400001000001000000000001000001000001004800000008000001000001000000000001000001000001004800000001000001000001000000000001000001000008004800000006404801004801000000000001000001000001120000000001000001000001000000000002c00001000006404800120002c04801000001000000000001000001000001000000120001000201000006400000000006400201000001004800000001000001000001000004800006404921000006404800000006400001000001000004800121000001000001004800120008000001000001000000000001000001000001004800000006400001000001000000000001000201000008004800000006404801004801000000000001004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120002c00001000006404800120006400201000001000004800001000001000002c00000000001124801000001004800000121004801000001000000000006400201000006400004800001000001000001000000120002c00006400001000000120001000001000001124800000001000001000001000000000006400201000008004800000006404801004801000000000001000001000001004800000006400001000001000000000002c0000100000640480012000800480640000100000012000100000100000100480012000640000100000100000000000640000100000640480012000640480100000100480480000,
  0x6400000000000000000000006400000000000000000000000000000000000000000000002c00000000000000000000000000000000000000000000006400000000000000000000000000200000002c00000000000000000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c00006400000000000000002c00000000006400000000006400200000000000000000000000000000002c00000000000000000000000000000000000000000000006400000000006400000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000006400000000000000000000000000000000000000000000000000000000000000000000002c00000000006400000000002c00000000000000000000000000000000000000000000000000200000006400000000006400200000000000000000000000000000000000000000006400000000006400000000006400000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000006400000000000000000000000000200000008000000000006400000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c00006400000000000000002c00000000006400000000006400200000000000000000000000000000002c00000000000000000000000000000000000000000000000000000000006400200000006400000000000000000000000000000000002c00006400000000000000000000000000000000000000000000000000000000000000006400200000008000000000006400000000000000000000000000000000000000000000006400000000000000000000002c0000000000640000000000800000640000000000000000000000000000000000000000640000000000000000000000640000000000640000000000640000000000000000000000
]

/-! ### States, the step and the check -/

/-- The block `0000001`, letter `p` at phase `p`. -/
def w0000001 : List Bool := [false, false, false, false, false, false, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `6 w .. 6 w + 5` of table
`8 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (8 * p + s) 0 >>> (6 * w)) % 64

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `00`, `0110`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 0) ||
    ((2 * s + b.toNat) % 16 == 6)

/-- The last 3 readings after a step from phase `p` with window `w`: at phase 2 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 2 then (2 * s + (w.testBit 0).toNat) % 8 else s

/-- The window of columns 1..10 after a step from phase `p`, with column 11 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 10 (w0000001.getD p false) z w

/-- The certificate at one state: ranks are at most 37; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 7) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 7) (sNext p s w) (wNext p w true)
  decide (r ≤ 37) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 2 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 1024

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 8 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 8 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 8 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 8 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 8 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 8 = true := by decide +kernel
theorem ok_6 : allBelowT (partOK 6) 8 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 7 → allBelowT (partOK p) 8 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | 6, _ => ok_6
  | p + 7, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 7) (hs : s < 8) (hw : w < 2 ^ 10) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 10 = 1024 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 37 ∧
      (rk p s w = 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 2 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `0000001` read from phase `ph`: letter `(t + ph) % 7` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w0000001.getD ((t + ph) % 7) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..10` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 10
  | t + 1 => stripStep 10 (F t 0) (F t 11) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 10 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 10).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last three readings of column 1 at the third white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 7) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 8
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 8
    unfold sNext
    cases ((t + ph) % 7 == 2)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 2) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 8

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 7) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 11) := by
  show stripStep 10 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `37 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 37 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 11)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 7 = ((t + ph) % 7 + 1) % 7 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 37 on, no reading at the third white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 37 ≤ t) (hp : (t + ph) % 7 = 2) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each third white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 7 = 2) :
    suf ph (drv (ctr ph) R) (t + 7) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 7) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  have h7 : suf ph (drv (ctr ph) R) (t + 7) = suf ph (drv (ctr ph) R) (t + 6) := by
    show sNext ((t + 6 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 6)) (win (drv (ctr ph) R) (t + 6)) = _
    exact sNext_ne (by omega)
  rw [h7, h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_00 : ∀ s, s < 8 → badB (push s false) false = true := by decide
theorem bad_0110 : ∀ s, s < 8 → badB (push (push (push s false) true) true) false = true := by decide

end ReadingWords.B0000001

open ReadingWords.B0000001

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `00`.** At the third white steps, column 1 never reads `00` with the first reading at time `30` or
later. -/
theorem no_00_time_0000001 (u : Nat) (hu : 30 ≤ u) (hp : (u + ph) % 7 = 2) :
    ¬ (drv (ctr ph) R u 1 = false ∧ drv (ctr ph) R (u + 7) 1 = false) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 7) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_00 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `0110`.** At the third white steps, column 1 never reads `0110` with the first reading at time `16` or
later. -/
theorem no_0110_time_0000001 (u : Nat) (hu : 16 ≤ u) (hp : (u + ph) % 7 = 2) :
    ¬ (drv (ctr ph) R u 1 = false ∧ drv (ctr ph) R (u + 7) 1 = true ∧ drv (ctr ph) R (u + 14) 1 = true ∧
      drv (ctr ph) R (u + 21) 1 = false) := by
  rintro ⟨h0, h1, h2, h3⟩
  rw [show u + 14 = u + 7 + 7 by omega] at h2
  rw [show u + 21 = u + 7 + 7 + 7 by omega] at h3
  have hb := no_bad R ph (u + 7 + 7 + 7) (by omega) (by omega)
  rw [suf_period R ph (u + 7 + 7) (by omega), suf_period R ph (u + 7) (by omega), suf_period R ph u hp, h0, h1, h2,
    h3] at hb
  rw [bad_0110 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B0000001

/-- A sequence of bits has none of the factors `00`, `0110` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = false ∧ b (i + 1) = false) ∧
    ¬ (b i = false ∧ b (i + 1) = true ∧ b (i + 2) = true ∧ b (i + 3) = false)

/-- Column 1 of the right half driven by `0000001` from phase `ph`, at the `i`-th third white step (the steps `t` with
`(t + ph) % 7 = 2`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (7 * i + (2 + 7 - ph % 7) % 7) 1

end ReadingWords.B0000001

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the third white steps avoid
`00`, `0110` from the 5th on. -/
theorem readings_0000001 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 5 := by
  intro i hi
  have hp : (7 * i + (2 + 7 - ph % 7) % 7 + ph) % 7 = 2 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (7 * i + (2 + 7 - ph % 7) % 7 + 7) 1 := by
    unfold reading; rw [show 7 * (i + 1) + (2 + 7 - ph % 7) % 7 = 7 * i + (2 + 7 - ph % 7) % 7 + 7 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (7 * i + (2 + 7 - ph % 7) % 7 + 14) 1 := by
    unfold reading; rw [show 7 * (i + 2) + (2 + 7 - ph % 7) % 7 = 7 * i + (2 + 7 - ph % 7) % 7 + 14 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (7 * i + (2 + 7 - ph % 7) % 7 + 21) 1 := by
    unfold reading; rw [show 7 * (i + 3) + (2 + 7 - ph % 7) % 7 = 7 * i + (2 + 7 - ph % 7) % 7 + 21 by omega]
  rw [e1, e2, e3]
  exact ⟨no_00_time_0000001 R ph _ (by omega) hp, no_0110_time_0000001 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `0000001` -/

namespace ReadingWords.B0000001

/-- From time `T` on, a row whose center column repeats `0000001` from `T` has the right half driven by `0000001` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0000001.getD ((t - T) % 7) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w0000001.getD ((0 + 0) % 7) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w0000001.getD ((t + 1 + 0) % 7) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B0000001

/-- **Readings of every row.** If the center column of a row repeats `0000001` from time `T` (letter
`(t - T) % 7` at time `t`), then column 1 at the times `T + 7 i + 2` avoids `00`, `0110` from `i = 5` on. -/
theorem readings_0000001_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0000001.getD ((t - T) % 7) false) :
    Avoids (fun i => evolve init (T + 7 * i + 2) 1) 5 := by
  have e : (fun i => evolve init (T + 7 * i + 2) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 7 * i + 2 = T + (7 * i + (2 + 7 - 0 % 7) % 7) by omega]
    exact evolve_eq_drv init T h (7 * i + (2 + 7 - 0 % 7) % 7) 1
  rw [e]
  exact readings_0000001 _ 0

end B0000001

/-! ## Block `0000101` -/

section B0000101

/-! The certificate and the helpers live in `ReadingWords.B0000101`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B0000101

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `2 * p + s` packs the rank of window `w` in bits `4 w .. 4 w + 3`. -/
def rankTabs : List Nat := [
  0x0,
  0x6,
  0x0,
  0x500000000000000000000000000000005,
  0x0,
  0x4000000000000000400000000000000040000000000000004,
  0x0,
  0x300000003000000030000000300000003000000030000000300000003,
  0x0,
  0x2000200020002000200020002000200020002000200020002000200020002,
  0x8000000000,
  0x1010101010101010101010101010101010101010101010101010108010101010,
  0x0,
  0x7000000000000000000000000000000070000000000000000000000000000000
]

/-! ### States, the step and the check -/

/-- The block `0000101`, letter `p` at phase `p`. -/
def w0000101 : List Bool := [false, false, false, false, true, false, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `4 w .. 4 w + 3` of table
`2 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (2 * p + s) 0 >>> (4 * w)) % 16

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `11`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 3)

/-- The last 1 readings after a step from phase `p` with window `w`: at phase 5 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 5 then (2 * s + (w.testBit 0).toNat) % 2 else s

/-- The window of columns 1..6 after a step from phase `p`, with column 7 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 6 (w0000101.getD p false) z w

/-- The certificate at one state: ranks are at most 8; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 7) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 7) (sNext p s w) (wNext p w true)
  decide (r ≤ 8) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 5 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 64

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 2 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 2 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 2 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 2 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 2 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 2 = true := by decide +kernel
theorem ok_6 : allBelowT (partOK 6) 2 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 7 → allBelowT (partOK p) 2 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | 6, _ => ok_6
  | p + 7, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 7) (hs : s < 2) (hw : w < 2 ^ 6) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 6 = 64 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 8 ∧
      (rk p s w = 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 5 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `0000101` read from phase `ph`: letter `(t + ph) % 7` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w0000101.getD ((t + ph) % 7) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..6` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 6
  | t + 1 => stripStep 6 (F t 0) (F t 7) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 6 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 6).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last one readings of column 1 at the fifth white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 7) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 2
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 2
    unfold sNext
    cases ((t + ph) % 7 == 5)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 5) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 2

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 7) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 7) := by
  show stripStep 6 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `8 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 8 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 7)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 7 = ((t + ph) % 7 + 1) % 7 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 8 on, no reading at the fifth white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 8 ≤ t) (hp : (t + ph) % 7 = 5) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each fifth white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 7 = 5) :
    suf ph (drv (ctr ph) R) (t + 7) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 7) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  have h7 : suf ph (drv (ctr ph) R) (t + 7) = suf ph (drv (ctr ph) R) (t + 6) := by
    show sNext ((t + 6 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 6)) (win (drv (ctr ph) R) (t + 6)) = _
    exact sNext_ne (by omega)
  rw [h7, h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_11 : ∀ s, s < 2 → badB (push s true) true = true := by decide

end ReadingWords.B0000101

open ReadingWords.B0000101

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `11`.** At the fifth white steps, column 1 never reads `11` with the first reading at time `1` or
later. -/
theorem no_11_time_0000101 (u : Nat) (hu : 1 ≤ u) (hp : (u + ph) % 7 = 5) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 7) 1 = true) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 7) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_11 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B0000101

/-- A sequence of bits has none of the factors `11` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true)

/-- Column 1 of the right half driven by `0000101` from phase `ph`, at the `i`-th fifth white step (the steps `t` with
`(t + ph) % 7 = 5`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (7 * i + (5 + 7 - ph % 7) % 7) 1

end ReadingWords.B0000101

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the fifth white steps avoid
`11` from the 1th on. -/
theorem readings_0000101 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 1 := by
  intro i hi
  have hp : (7 * i + (5 + 7 - ph % 7) % 7 + ph) % 7 = 5 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (7 * i + (5 + 7 - ph % 7) % 7 + 7) 1 := by
    unfold reading; rw [show 7 * (i + 1) + (5 + 7 - ph % 7) % 7 = 7 * i + (5 + 7 - ph % 7) % 7 + 7 by omega]
  rw [e1]
  exact no_11_time_0000101 R ph _ (by omega) hp

/-! ### Every row whose center column repeats `0000101` -/

namespace ReadingWords.B0000101

/-- From time `T` on, a row whose center column repeats `0000101` from `T` has the right half driven by `0000101` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0000101.getD ((t - T) % 7) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w0000101.getD ((0 + 0) % 7) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w0000101.getD ((t + 1 + 0) % 7) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B0000101

/-- **Readings of every row.** If the center column of a row repeats `0000101` from time `T` (letter
`(t - T) % 7` at time `t`), then column 1 at the times `T + 7 i + 5` avoids `11` from `i = 1` on. -/
theorem readings_0000101_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0000101.getD ((t - T) % 7) false) :
    Avoids (fun i => evolve init (T + 7 * i + 5) 1) 1 := by
  have e : (fun i => evolve init (T + 7 * i + 5) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 7 * i + 5 = T + (7 * i + (5 + 7 - 0 % 7) % 7) by omega]
    exact evolve_eq_drv init T h (7 * i + (5 + 7 - 0 % 7) % 7) 1
  rw [e]
  exact readings_0000101 _ 0

end B0000101

/-! ## Block `0001001` -/

section B0001001

/-! The certificate and the helpers live in `ReadingWords.B0001001`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B0001001

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `2 * p + s` packs the rank of window `w` in bits `6 w .. 6 w + 5`. -/
def rankTabs : List Nat := [
  0x2000000000000000000000000000000000000000000000003d600000000000000000000000000000000000000000000020000000000000000000000001d00000000000000000000020000000000000000000000000000000000000000000000020000000000000000f00000000000000000000000000000020000000000000000000000000000000000000000000000020000000000000000000000001d00000000000000000000020000000000000000000000f00000000000000000000000020000000000000000f0000000000000000000000000000003d600000000000000000000000000000000000000000000020000000000000000000000001d00000000000000000000020000000000000000000000000000000000000000000000020000000000000000000000001d0000000000000000000002000000000000000000000000000000000000000000000003d600000000000000000000001d0000000000000000000003d6000000000000000000000000,
  0x400400400400400400402000400400400400400400400400400400400400400400403d604004004004004004004004004004004004004004004020004004004004004004004005d04004004004004004004020004004004004004004004004004004004004004004004020004004004004004f04004004004004004004004004004020004004004004004004004004004004004004004004004020004004004004004004004005d04004004004004004004020004004004004004004004f04004004004004004004004020004004004004004f0400400400400400400400400400403d604004004004004004004004004004004004004004004020004004004004004004004005d04004004004004004004020004004004004004004004004004004004004004004004020004004004004004004004005d0400400400400400400402000400400400400400400400400400400400400400400403d604004004004004004004005d0400400400400400400403d6040040040040040040040040,
  0x1c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000000000000000038001500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000001c000000000000000000000000000000380015000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x1c000000000000001c0000001c00001c00000000000000001c00000000000000000000001c00001c00000000000000001c000000000000001c0000001c00001c00000000000000001c00000000000000000000001c00003800000000000000001c000000000000001c0000001c00001c00000000000000001c00000000000000000000001c00001c00000000000000003800150000000000000000001c00001c00000000000000001c00000000000000000000001c00001c00000000000000001c000000000000001c0000001c00001c00000000000000001c00000000000000000000001c00001c00000000000000001c000000000000001c0000001c00001c00000000000000001c00000000000000000000001c00003800000000000000001c000000000000001c0000001c00001c00000000000000003800150000000000000000001c00001c00000000000000001c00000000000000000000001c00001c00000000000000001c00000000000000000000001c00001c0000000000,
  0x1b00000000000000000000000000000000000000001400034000000000000000000000000000000000000000000000001b00000000000000000000001b00000000000000000000002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00000000000000000000001b00001400d00000000000000000000000000000000000000000000000000000000000001b00000000000000000000000000000000000000001400034000000000000000000000000000000000000000000000001b00000000000000000000001b00000000000000000000002200000000000000000000000000000000000000000000001b00000000000000000000000000000000000000000000002200000000000000000000000000000000000000000000001b00000000000000000000001b00000000000000000000001b000014000000,
  0x18000000000600000000000019b00000000600000000000018000000000600000001400034000000000000000000000018000000000600000000000019b00000000600000000000019b0000000060000000000001a200000000000000000000018000000000600000000000018000000000600000000000018000000000600000000000018000000000000000000000018000000000600000000000019b00000000600000000000019b00001400d00000000000018000000000000000000000018000000000600000000000019b00000000600000000000018000000000600000001400034000000000000000000000018000000000600000000000019b00000000600000000000019b0000000060000000000001a200000000000000000000018000000000600000000000019b0000000060000000000001800000000060000000000001a200000000000000000000018000000000600000000000019b00000000600000000000019b00000000600000000000019b000014000000,
  0x2100000000000000000000001a00000000000000000000002100000000000000000000000000000000000000000030000000000001300000000000001a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00000000000000000000000000000000000000000000000000000000000000000000002100000000000000000000000000000000000000000000001a00000000000000000001300000000000000000000000002100000000000000000000001a00000000000000000000002100000000000000000000000000000000000000000030000000000001300000000000001a00000000000000000000000000000000000000000000000000000000000000000030000000000001300000000000001a00000000000000000000002100000000000000000000000000000000000000000000002100000000000000000000001a00000000000000000000001a000000000000000000000000000000000000000000,
  0x14002100000014000000000014001a00000000000000000014002100000014000000000014000000000000000000000030000000000015300000000014001a00000000000000000014000000000014000000000014000000000000000000000014000000000014000000000014001a00000000000000000014000000000014000000000014000000000000000000000014002100000014000000000014000000000000000000000014001a00000014000000000015300000000000000000000014002100000014000000000014001a00000000000000000014002100000014000000000014000000000000000000000030000000000015300000000014001a00000000000000000014000000000014000000000014000000000000000000000030000000000015300000000014001a00000000000000000014002100000014000000000014000000000000000000000014002100000014000000000014001a00000000000000000014001a000000140000000000140000000000000000000000,
  0x80000000000000000000000080000000000000000000000000000000000000000000000064000080000000000000000000000000000000000000000080000064000000000000000080000000000001200000000000000000000000000b00000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000064000000000000000080000000000000000000000080000000000000000000000080000000000000000000000080000000000000000000000000000000000000000000000064000080000000000000000000000000000000000000000080000064000000000000000080000000000001200000000000000000000000000b000000000000000000000000000000800000640000000000000000000000000000000000000000640480800000000000000000000000000000000000000000800000640000000000000000800000000000000000000000800000800000000000,
  0x80000000000000000400000080000000000000000400000000000000000000000400000064000080000000000400000000000000000000000400000080000064000000000400000080000000000001200400000000000000000000000b00000000000000000000000400000080000000000000000400000000000000000000000400000000000000000000000400000000000000000000000400000080000064000000000400000080000000000000000400000080000000000000000400000080000000000000000400000080000000000000000400000000000000000000000400000064000080000000000400000000000000000000000400000080000064000000000400000080000000000001200400000000000000000000000b000000000000000000000004000000800000640000000004000000000000000000000004000000640480800000000004000000000000000000000004000000800000640000000004000000800000000000000004000000800000800000000004,
  0x44000000060000000001f0000000000007c000000000000000000000000000000000000000000000000000000000000a0000000006000000000000000000000007c00000000000000000000007c000000000000000000000000000000000000000000000000000000001f00000000000000000000001800000000000000000000000000000000000000000000000000a0000000000000000000000000000000007c00000000180000000000007c000000000000000000000000000000000000044000000060000000001f0000000000007c000000001800000000000000000000000000000000000000000000000000a0000000006000000000000000000000007c00000000000000000000007c00000000000000000000000000000000000000000000006000000000000000000000007c00000000000000000000000000000000000000000000000000000000000110000000000000000000000000000000007c00000110000000000000007c00000000000000000000007c0000000000000,
  0x44000000060300000001f0030000000007c300000000000300000000000300000000000300000000000300000000000a0000000006030000000000030000000007c30000000000030000000007c300000000000300000000000300000000000300000000000300000001f00300000000000300000001800300000000000300000000000300000000000300000000000a0000000000030000000000030000000007c30000000180030000000007c300000000000300000000000300000000000344000000060300000001f0030000000007c300000001800300000000000300000000000300000000000300000000000a0000000006030000000000030000000007c30000000000030000000007c30000000000030000000000030000000000030000000006030000000000030000000007c30000000000030000000000030000000000030000000000030000000000110000000000030000000000030000000007c30000110000030000000007c30000000000030000000007c3000000000003,
  0x5c00000000007800000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000007800000000000000000000090000000000000000000000005c00000000000000000000000100000000000000000000007800000000000000000000090000000000000000000000000000000000000000000100000000000000005c00000000000000000000000000000000097800000000000000000000000000000000000000000000000100000000005c00000000007800000000000000000000100000000000000000000000000000000000000000000100000000000000000000000000007800000000000000000000090000000000000000000000005c00000000000000000000000000000000000000000000007800000000000000000000090000000000005c00000000000000000000000000000100000000000000000000000000007800000000000000000000097800000000005c00000000005c0000000000000000000400,
  0x20000025c00020000027800020000020000020000100000020000020000020000020000020000020000020000020000020000020000020000027800020000020000020000090000020000020000020000025c00020000020000020000020100020000020000020000027800020000020000020000090000020000020000020000020000020000020000020100020000020000025c00020000020000020000020000020000097800020000020000020000020000020000020000020000020100020000025c00020000027800020000020000020000100000020000020000020000020000020000020000020100020000020000020000020000027800020000020000020000090000020000020000020000025c00020000020000020000020000020000020000020000027800020000020000020000090000020000025c00020000020000020000020000020100020000020000020000020000027800020000020000020000097800020000025c00020000025c0002000002000002000402
]

/-! ### States, the step and the check -/

/-- The block `0001001`, letter `p` at phase `p`. -/
def w0001001 : List Bool := [false, false, false, true, false, false, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `6 w .. 6 w + 5` of table
`2 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (2 * p + s) 0 >>> (6 * w)) % 64

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `11`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 3)

/-- The last 1 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 2 else s

/-- The window of columns 1..9 after a step from phase `p`, with column 10 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 9 (w0001001.getD p false) z w

/-- The certificate at one state: ranks are at most 34; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 7) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 7) (sNext p s w) (wNext p w true)
  decide (r ≤ 34) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 512

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 2 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 2 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 2 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 2 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 2 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 2 = true := by decide +kernel
theorem ok_6 : allBelowT (partOK 6) 2 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 7 → allBelowT (partOK p) 2 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | 6, _ => ok_6
  | p + 7, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 7) (hs : s < 2) (hw : w < 2 ^ 9) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 9 = 512 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 34 ∧
      (rk p s w = 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `0001001` read from phase `ph`: letter `(t + ph) % 7` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w0001001.getD ((t + ph) % 7) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..9` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 9
  | t + 1 => stripStep 9 (F t 0) (F t 10) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 9 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 9).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last one readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 7) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 2
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 2
    unfold sNext
    cases ((t + ph) % 7 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 2

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 7) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 10) := by
  show stripStep 9 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `34 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 34 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 10)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 7 = ((t + ph) % 7 + 1) % 7 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 34 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 34 ≤ t) (hp : (t + ph) % 7 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 7 = 0) :
    suf ph (drv (ctr ph) R) (t + 7) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 7) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  have h7 : suf ph (drv (ctr ph) R) (t + 7) = suf ph (drv (ctr ph) R) (t + 6) := by
    show sNext ((t + 6 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 6)) (win (drv (ctr ph) R) (t + 6)) = _
    exact sNext_ne (by omega)
  rw [h7, h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_11 : ∀ s, s < 2 → badB (push s true) true = true := by decide

end ReadingWords.B0001001

open ReadingWords.B0001001

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `11`.** At the first white steps, column 1 never reads `11` with the first reading at time `27` or
later. -/
theorem no_11_time_0001001 (u : Nat) (hu : 27 ≤ u) (hp : (u + ph) % 7 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 7) 1 = true) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 7) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_11 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B0001001

/-- A sequence of bits has none of the factors `11` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true)

/-- Column 1 of the right half driven by `0001001` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 7 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (7 * i + (7 - ph % 7) % 7) 1

end ReadingWords.B0001001

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`11` from the 4th on. -/
theorem readings_0001001 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 4 := by
  intro i hi
  have hp : (7 * i + (7 - ph % 7) % 7 + ph) % 7 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 7) 1 := by
    unfold reading; rw [show 7 * (i + 1) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 7 by omega]
  rw [e1]
  exact no_11_time_0001001 R ph _ (by omega) hp

/-! ### Every row whose center column repeats `0001001` -/

namespace ReadingWords.B0001001

/-- From time `T` on, a row whose center column repeats `0001001` from `T` has the right half driven by `0001001` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0001001.getD ((t - T) % 7) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w0001001.getD ((0 + 0) % 7) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w0001001.getD ((t + 1 + 0) % 7) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B0001001

/-- **Readings of every row.** If the center column of a row repeats `0001001` from time `T` (letter
`(t - T) % 7` at time `t`), then column 1 at the times `T + 7 i` avoids `11` from `i = 4` on. -/
theorem readings_0001001_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0001001.getD ((t - T) % 7) false) :
    Avoids (fun i => evolve init (T + 7 * i) 1) 4 := by
  have e : (fun i => evolve init (T + 7 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 7 * i = T + (7 * i + (7 - 0 % 7) % 7) by omega]
    exact evolve_eq_drv init T h (7 * i + (7 - 0 % 7) % 7) 1
  rw [e]
  exact readings_0001001 _ 0

end B0001001

/-! ## Block `0001011` -/

section B0001011

/-! The certificate and the helpers live in `ReadingWords.B0001011`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B0001011

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `16 * p + s` packs the rank of window `w` in bits `6 w .. 6 w + 5`. -/
def rankTabs : List Nat := [
  0x90074000000000000000000090000000000000000000000000000000000000074000000000000090000000002b00002b00058000000000000000000090000000000000000000000090000000000000002400000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000074000000000000000000000000000000000000000000000074000000090000000000000000000000090000000000000000000000090000000000000000000000090074000000000000000000090000000000000000000000000000000000000074000000000000090000000002b00002b00058000000000000000000090000000000000000000000090000000000000002400000000000000000000000000002b00058000000000000000000090000000000000000000000000000000000000074000000000000090000000000000000000000000000000074000000090000000000000000000000090000000000000074000000090000090000000002b,
  0x890074000000000000800000890001600000000000000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800000800000000000000000800000890000000000001600000000800000000000000074800000000000f00000000000800000800000000000000074800000890000000000001600000000890000000000000000800000090001600000000000800000890074000000000000800000890001600000001600000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800002b00058000000000000800000890000000000000000000000800000000000000074800000000000f90000000000800000800000000000000074800000890000000000000000000000890001600000000074800000090000090000000002b,
  0x4004890074004004004004804004890004004004004004004004804004004004004074804004004004f90004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804004804004004004004004804004890004004004004004004004804004004004004074804004004004f04004004004804004804004004004004074804004890004004004004004004004890004004004004004804004090004004004004004804004890074004004004004804004890004004004004004004004804004004004004074804004004004f90004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804006b04058004004004004804004890004004004004004004004804004004004004074804004004004f90004004004804004804004004004004074804004890004004004004004004004890004004004004074804004090004090004004006b,
  0x890074000000000000800000890001600000000000000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800000800000000000000000800000890000000000001600000000800000000000000074800000000000f00000000000800000800000000000000074800000890000000000001600000000890000000000000000800000090001600000000000800000890074000000000000800000890001600000001600000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800002b00058000000000000800000890000000000000000000000800000000000000074800000000000f90000000000800000800000000000000074800000890000000000000000000000890001600000000074800000090000090000000002b,
  0x4004890074004004004004804004890004004004004004004004804004004004004074804004004004090004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804004804004004004004004804004890004004004004004004004804004004004004074804004004004004004004004804004804004004004004074804004890004004004004004004004890004004004004004804004090004004004004004804004890074004004004004804004890004004004004004004004804004004004004074804004004004090004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804006b04058004004004004804004890004004004004004004004804004004004004074804004004004090004004004804004804004004004004074804004890004004004004004004004890004004004004074804004090004090004004006b,
  0x890074000000000000800000890001600000000000000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800000800000000000000000800000890000000000001600000000800000000000000074800000000000f00000000000800000800000000000000074800000890000000000001600000000890000000000000000800000090001600000000000800000890074000000000000800000890001600000001600000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800002b00058000000000000800000890000000000000000000000800000000000000074800000000000f90000000000800000800000000000000074800000890000000000000000000000890001600000000074800000090000090000000002b,
  0x4004890074004004004004804004890004004004004004004004804004004004004074804004004004f90004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804004804004004004004004804004890004004004004004004004804004004004004074804004004004f04004004004804004804004004004004074804004890004004004004004004004890004004004004004804004090004004004004004804004890074004004004004804004890004004004004004004004804004004004004074804004004004f90004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804006b04058004004004004804004890004004004004004004004804004004004004074804004004004f90004004004804004804004004004004074804004890004004004004004004004890004004004004074804004090004090004004006b,
  0x890074000000000000800000890001600000000000000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800000800000000000000000800000890000000000001600000000800000000000000074800000000000f00000000000800000800000000000000074800000890000000000001600000000890000000000000000800000090001600000000000800000890074000000000000800000890001600000001600000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800002b00058000000000000800000890000000000000000000000800000000000000074800000000000f90000000000800000800000000000000074800000890000000000000000000000890001600000000074800000090000090000000002b,
  0x4004090074004004004004004004090004004004004004004004004004004004004074004004004004090004004006b04006b04058004004004004004004090004004004004004004004090004004004004006404004004004004004004004004004004004004004004004004004090004004004004004004004004004004004004074004004004004004004004004004004004004004004004074004004090004004004004004004004090004004004004004004004090004004004004004004004090074004004004004004004090004004004004004004004004004004004004074004004004004090004004006b04006b04058004004004004004004090004004004004004004004090004004004004006404004004004004004004004004006b04058004004004004004004090004004004004004004004004004004004004074004004004004090004004004004004004004004004004074004004090004004004004004004004090004004004004074004004090004090004004006b,
  0x890074000000000000800000890001600000000000000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800000800000000000000000800000890000000000001600000000800000000000000074800000000000f00000000000800000800000000000000074800000890000000000001600000000890000000000000000800000090001600000000000800000890074000000000000800000890001600000001600000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800002b00058000000000000800000890000000000000000000000800000000000000074800000000000f90000000000800000800000000000000074800000890000000000000000000000890001600000000074800000090000090000000002b,
  0x4004890074004004004004804004890004004004004004004004804004004004004074804004004004f90004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804004804004004004004004804004890004004004004004004004804004004004004074804004004004f04004004004804004804004004004004074804004890004004004004004004004890004004004004004804004090004004004004004804004890074004004004004804004890004004004004004004004804004004004004074804004004004f90004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804006b04058004004004004804004890004004004004004004004804004004004004074804004004004f90004004004804004804004004004004074804004890004004004004004004004890004004004004074804004090004090004004006b,
  0x890074000000000000800000890001600000000000000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800000800000000000000000800000890000000000001600000000800000000000000074800000000000f00000000000800000800000000000000074800000890000000000001600000000890000000000000000800000090001600000000000800000890074000000000000800000890001600000001600000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800002b00058000000000000800000890000000000000000000000800000000000000074800000000000f90000000000800000800000000000000074800000890000000000000000000000890001600000000074800000090000090000000002b,
  0x4004890074004004004004804004890004004004004004004004804004004004004074804004004004090004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804004804004004004004004804004890004004004004004004004804004004004004074804004004004004004004004804004804004004004004074804004890004004004004004004004890004004004004004804004090004004004004004804004890074004004004004804004890004004004004004004004804004004004004074804004004004090004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804006b04058004004004004804004890004004004004004004004804004004004004074804004004004090004004004804004804004004004004074804004890004004004004004004004890004004004004074804004090004090004004006b,
  0x890074000000000000800000890001600000000000000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800000800000000000000000800000890000000000001600000000800000000000000074800000000000f00000000000800000800000000000000074800000890000000000001600000000890000000000000000800000090001600000000000800000890074000000000000800000890001600000001600000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800002b00058000000000000800000890000000000000000000000800000000000000074800000000000f90000000000800000800000000000000074800000890000000000000000000000890001600000000074800000090000090000000002b,
  0x4004890074004004004004804004890004004004004004004004804004004004004074804004004004f90004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804004804004004004004004804004890004004004004004004004804004004004004074804004004004f04004004004804004804004004004004074804004890004004004004004004004890004004004004004804004090004004004004004804004890074004004004004804004890004004004004004004004804004004004004074804004004004f90004004006b04006b04058004004004004804004890004004004004004004004890004004004004006404004004004004004004004804006b04058004004004004804004890004004004004004004004804004004004004074804004004004f90004004004804004804004004004004074804004890004004004004004004004890004004004004074804004090004090004004006b,
  0x890074000000000000800000890001600000000000000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800000800000000000000000800000890000000000001600000000800000000000000074800000000000f00000000000800000800000000000000074800000890000000000001600000000890000000000000000800000090001600000000000800000890074000000000000800000890001600000001600000000800000000000000074800000000000f90000000002b00002b00058000000000000800000890000000000000000000000890000000000000002400000000000000000000000800002b00058000000000000800000890000000000000000000000800000000000000074800000000000f90000000000800000800000000000000074800000890000000000000000000000890001600000000074800000090000090000000002b,
  0x230000000230000000000008c000000000000000000002a00000000002300000000000000000000002a0000000000000000000000000000000000008c000000000002a0000000008c000000000000000000000000002a00000000000000000000000000002300000000000000000000000000000000002a00000000000000000000000000000000000000000000002a0000000000000000000000008c000000000002a0000000008c000000000000000000000000000000000002a0000000000230000000230000000000008c000000000000000000002a00000000002300000000000000000000002a0000000000000000000000000000000000008c000000000002a0000000008c000000000000000000000000002a0000000000000000000000000000000000000000008c000000000002a00000002a00000000000000000000000000000000000000000000002a0000000000230000000000008c000000000002a0000000008c00000000230000000000008c0000000000000,
  0x2370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000070000002300000000000000000000000000000000072a00000000000000000000000000000000000000000000002a00054000000000000001c0008c000000000002a00001c0008c000000000000000000000000000000000002a00000e00002370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000000000000000000001c0008c000000000002a00000072a00054000000000000000000000000000000000000000072a00070000002300000001c0008c000000000002a00001c0008c07000000230007000000008c0000000000000,
  0x71e35400000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000150078c70000000071c05400000071c702a00000700700000e0071c70000000231c00000000071c700700000700700000002a1c70000000071c00000000071c700700000700700000002a1c75400000071c00000000078c700700000702a0000000078c70000000071c00000000071c700700000702a00000e0071e35400000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000150078c70000000071c05400000071c702a00000700700000e0071c70000000071c00000000078c700700000702a00000002a1c75400000071c00000000071c700700000700700000002a1c70000000231c00000150078c700700000702a0000000078c75400000231c05400000078c7007000007007,
  0x2370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000070000002300000000000000000000000000000000072a00000000000000000000000000000000000000000000002a00054000000000000001c0008c000000000002a00001c0008c000000000000000000000000000000000002a00000e00002370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000000000000000000001c0008c000000000002a00000072a00054000000000000000000000000000000000000000072a00070000002300000001c0008c000000000002a00001c0008c07000000230007000000008c0000000000000,
  0x71e30000000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c702a00000700700000e0071c70000000231c00000000071c700700000700700000002a1c70000000071c00000000071c700700000700700000002a1c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c700700000702a00000e0071e30000000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c702a00000700700000e0071c70000000071c00000000078c700700000702a00000002a1c70000000071c00000000071c700700000700700000002a1c70000000231c00000000078c700700000702a0000000078c70000000231c00000000078c7007000007007,
  0x2370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000070000002300000000000000000000000000000000072a00000000000000000000000000000000000000000000002a00054000000000000001c0008c000000000002a00001c0008c000000000000000000000000000000000002a00000e00002370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000000000000000000001c0008c000000000002a00000072a00054000000000000000000000000000000000000000072a00070000002300000001c0008c000000000002a00001c0008c07000000230007000000008c0000000000000,
  0x71e35400000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000150078c70000000071c05400000071c702a00000700700000e0071c70000000231c00000000071c700700000700700000002a1c70000000071c00000000071c700700000700700000002a1c75400000071c00000000078c700700000702a0000000078c70000000071c00000000071c700700000702a00000e0071e35400000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000150078c70000000071c05400000071c702a00000700700000e0071c70000000071c00000000078c700700000702a00000002a1c75400000071c00000000071c700700000700700000002a1c70000000231c00000150078c700700000702a0000000078c75400000231c05400000078c7007000007007,
  0x2370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000070000002300000000000000000000000000000000072a00000000000000000000000000000000000000000000002a00054000000000000001c0008c000000000002a00001c0008c000000000000000000000000000000000002a00000e00002370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000000000000000000001c0008c000000000002a00000072a00054000000000000000000000000000000000000000072a00070000002300000001c0008c000000000002a00001c0008c07000000230007000000008c0000000000000,
  0x71e30000000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a0070000000071c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c702a0000070070000000071c70000000231c00000000071c700700000700700000002a1c70000000071c00000000071c700700000700700000002a1c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c700700000702a0000000071e30000000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a0070000000071c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c702a0000070070000000071c70000000071c00000000078c700700000702a00000002a1c70000000071c00000000071c700700000700700000002a1c70000000231c00000000078c700700000702a0000000078c70000000231c00000000078c7007000007007,
  0x2370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000070000002300000000000000000000000000000000072a00000000000000000000000000000000000000000000002a00054000000000000001c0008c000000000002a00001c0008c000000000000000000000000000000000002a00000e00002370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000000000000000000001c0008c000000000002a00000072a00054000000000000000000000000000000000000000072a00070000002300000001c0008c000000000002a00001c0008c07000000230007000000008c0000000000000,
  0x71e35400000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000150078c70000000071c05400000071c702a00000700700000e0071c70000000231c00000000071c700700000700700000002a1c70000000071c00000000071c700700000700700000002a1c75400000071c00000000078c700700000702a0000000078c70000000071c00000000071c700700000702a00000e0071e35400000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000150078c70000000071c05400000071c702a00000700700000e0071c70000000071c00000000078c700700000702a00000002a1c75400000071c00000000071c700700000700700000002a1c70000000231c00000150078c700700000702a0000000078c75400000231c05400000078c7007000007007,
  0x2370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000070000002300000000000000000000000000000000072a00000000000000000000000000000000000000000000002a00054000000000000001c0008c000000000002a00001c0008c000000000000000000000000000000000002a00000e00002370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000000000000000000001c0008c000000000002a00000072a00054000000000000000000000000000000000000000072a00070000002300000001c0008c000000000002a00001c0008c07000000230007000000008c0000000000000,
  0x71e30000000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c702a00000700700000e0071c70000000231c00000000071c700700000700700000002a1c70000000071c00000000071c700700000700700000002a1c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c700700000702a00000e0071e30000000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000000078c70000000071c00000000071c702a00000700700000e0071c70000000071c00000000078c700700000702a00000002a1c70000000071c00000000071c700700000700700000002a1c70000000231c00000000078c700700000702a0000000078c70000000231c00000000078c7007000007007,
  0x2370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000070000002300000000000000000000000000000000072a00000000000000000000000000000000000000000000002a00054000000000000001c0008c000000000002a00001c0008c000000000000000000000000000000000002a00000e00002370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000000000000000000001c0008c000000000002a00000072a00054000000000000000000000000000000000000000072a00070000002300000001c0008c000000000002a00001c0008c07000000230007000000008c0000000000000,
  0x71e35400000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000150078c70000000071c05400000071c702a00000700700000e0071c70000000231c00000000071c700700000700700000002a1c70000000071c00000000071c700700000700700000002a1c75400000071c00000000078c700700000702a0000000078c70000000071c00000000071c700700000702a00000e0071e35400000231c00000000078c700700000700700000002a1c70000000231c00000000071c700700002a00700000e0071c70000000071c00000000078c700700000702a0000150078c70000000071c05400000071c702a00000700700000e0071c70000000071c00000000078c700700000702a00000002a1c75400000071c00000000071c700700000700700000002a1c70000000231c00000150078c700700000702a0000000078c75400000231c05400000078c7007000007007,
  0x2370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000070000002300000000000000000000000000000000072a00000000000000000000000000000000000000000000002a00054000000000000001c0008c000000000002a00001c0008c000000000000000000000000000000000002a00000e00002370000002300000001c0008c000000000000000000072a00070000002300000000000000000000002a00000000e00000000000000000000001c0008c000000000002a00001c0008c000000000000054000000000072a00000000000000e00000000000000000000001c0008c000000000002a00000072a00054000000000000000000000000000000000000000072a00070000002300000001c0008c000000000002a00001c0008c07000000230007000000008c0000000000000,
  0x29880000000000000000000000000000000000000000000000000000a40000000022000000000000000000000000000029880000000000a40000000000000000000000000000000000000000000000000022000029000000000000000022000000000000000000000000000000000000000000000000000000000000a40000000000029000880000000000000000000000000000000000a40000000022880000000000000000000000000000000000000000000000000000000000000022000029880000000000000000000000000000000000000000000000000000a40000000022029000000000000000000000000029880000000000a40000000000000000000000000000000000000000000000000022000029000000000000000000000029880000000000a40000000000880000000000000000000000000000a40000000022029000000000000000000000000000880000000000a40000000000880000000000000000000000000022000000000000000000,
  0x2988000000000001b00000000000000000d000000000000500000000a5b00000002200d00000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000000000002200000000000000000001400000000000000000d000000000000000000000a406c000000002900088000000d0000000000006c0000000000000a400000000228800000000000000000006c000000000000000d00001400000000000000000002200002988000000000001b00000000000000000d000000000000500000000a5b6c000002202900000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000d000000000000029880000000000a5b00000000088000000d0000000000006c0000000a406db00002202900000000000d000000000000500880000000000a5b0000000008800000000000000000006c000002200000000000001b000,
  0x18000618000018000600002988000618000018000600000618000618d000180006000506180006a4000018002200d00618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618000018002200000618000618000019400600000618000618d000180006000006180006a4000018000602900688000618d000180006000006180006180000a4000600002288000618000018000600000618000618000018d00601400618000618000018002200002988000618000019400600000618000618d000180006000506180006a4000018002202900618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618d000180006000029880006180000a4000600000688000618d000180006000006180006a4000018002202900618000618d000180006000506880006180000a40006000006880006180000180006000506180022180000180006000006,
  0x2988000000000001b00000000000000000d000000000000500000000a5b00000002200d00000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000000000002200000000000000000001400000000000000000d000000000000000000000a406c000000002900088000000d0000000000006c0000000000000a400000000228800000000000000000006c000000000000000d00001400000000000000000002200002988000000000001b00000000000000000d000000000000500000000a5b6c000002202900000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000d000000000000029880000000000a5b00000000088000000d0000000000006c0000000a406db00002202900000000000d000000000000500880000000000a5b0000000008800000000000000000006c000002200000000000001b000,
  0x18000618000018000600002988000618000018000600000618000618d000180006000006180006a4000018002200d00618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618000018002200000618000618000018000600000618000618d000180006000006180006a4000018000602900688000618d000180006000006180006180000a4000600002288000618000018000600000618000618000018d00600000618000618000018002200002988000618000018000600000618000618d000180006000006180006a4000018002202900618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618d000180006000029880006180000a4000600000688000618d000180006000006180006a4000018002202900618000618d000180006000006880006180000a40006000006880006180000180006000006180022180000180006000006,
  0x2988000000000001b00000000000000000d000000000000500000000a5b00000002200d00000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000000000002200000000000000000001400000000000000000d000000000000000000000a406c000000002900088000000d0000000000006c0000000000000a400000000228800000000000000000006c000000000000000d00001400000000000000000002200002988000000000001b00000000000000000d000000000000500000000a5b6c000002202900000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000d000000000000029880000000000a5b00000000088000000d0000000000006c0000000a406db00002202900000000000d000000000000500880000000000a5b0000000008800000000000000000006c000002200000000000001b000,
  0x18000618000018000600002988000618000018000600000618000618d000180006000506180006a4000018002200d00618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618000018002200000618000618000019400600000618000618d000180006000006180006a4000018000602900688000618d000180006000006180006180000a4000600002288000618000018000600000618000618000018d00601400618000618000018002200002988000618000019400600000618000618d000180006000506180006a4000018002202900618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618d000180006000029880006180000a4000600000688000618d000180006000006180006a4000018002202900618000618d000180006000506880006180000a40006000006880006180000180006000506180022180000180006000006,
  0x2988000000000001b00000000000000000d000000000000500000000a5b00000002200d00000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000000000002200000000000000000001400000000000000000d000000000000000000000a406c000000002900088000000d0000000000006c0000000000000a400000000228800000000000000000006c000000000000000d00001400000000000000000002200002988000000000001b00000000000000000d000000000000500000000a5b6c000002202900000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000d000000000000029880000000000a5b00000000088000000d0000000000006c0000000a406db00002202900000000000d000000000000500880000000000a5b0000000008800000000000000000006c000002200000000000001b000,
  0x180006180000180006000029880006180000180006000006180006180000180006000006180006a40000180022000006180006180000180006000029880006180000a40006000006180006180000180006000006180006180000180022000029180006180000180022000006180006180000180006000006180006180000180006000006180006a40000180006029006880006180000180006000006180006180000a40006000022880006180000180006000006180006180000180006000006180006180000180022000029880006180000180006000006180006180000180006000006180006a40000180022029006180006180000180006000029880006180000a40006000006180006180000180006000006180006180000180022000029180006180000180006000029880006180000a40006000006880006180000180006000006180006a40000180022029006180006180000180006000006880006180000a40006000006880006180000180006000006180022180000180006000006,
  0x2988000000000001b00000000000000000d000000000000500000000a5b00000002200d00000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000000000002200000000000000000001400000000000000000d000000000000000000000a406c000000002900088000000d0000000000006c0000000000000a400000000228800000000000000000006c000000000000000d00001400000000000000000002200002988000000000001b00000000000000000d000000000000500000000a5b6c000002202900000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000d000000000000029880000000000a5b00000000088000000d0000000000006c0000000a406db00002202900000000000d000000000000500880000000000a5b0000000008800000000000000000006c000002200000000000001b000,
  0x18000618000018000600002988000618000018000600000618000618d000180006000506180006a4000018002200d00618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618000018002200000618000618000019400600000618000618d000180006000006180006a4000018000602900688000618d000180006000006180006180000a4000600002288000618000018000600000618000618000018d00601400618000618000018002200002988000618000019400600000618000618d000180006000506180006a4000018002202900618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618d000180006000029880006180000a4000600000688000618d000180006000006180006a4000018002202900618000618d000180006000506880006180000a40006000006880006180000180006000506180022180000180006000006,
  0x2988000000000001b00000000000000000d000000000000500000000a5b00000002200d00000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000000000002200000000000000000001400000000000000000d000000000000000000000a406c000000002900088000000d0000000000006c0000000000000a400000000228800000000000000000006c000000000000000d00001400000000000000000002200002988000000000001b00000000000000000d000000000000500000000a5b6c000002202900000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000d000000000000029880000000000a5b00000000088000000d0000000000006c0000000a406db00002202900000000000d000000000000500880000000000a5b0000000008800000000000000000006c000002200000000000001b000,
  0x18000618000018000600002988000618000018000600000618000618d000180006000006180006a4000018002200d00618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618000018002200000618000618000018000600000618000618d000180006000006180006a4000018000602900688000618d000180006000006180006180000a4000600002288000618000018000600000618000618000018d00600000618000618000018002200002988000618000018000600000618000618d000180006000006180006a4000018002202900618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618d000180006000029880006180000a4000600000688000618d000180006000006180006a4000018002202900618000618d000180006000006880006180000a40006000006880006180000180006000006180022180000180006000006,
  0x2988000000000001b00000000000000000d000000000000500000000a5b00000002200d00000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000000000002200000000000000000001400000000000000000d000000000000000000000a406c000000002900088000000d0000000000006c0000000000000a400000000228800000000000000000006c000000000000000d00001400000000000000000002200002988000000000001b00000000000000000d000000000000500000000a5b6c000002202900000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000d000000000000029880000000000a5b00000000088000000d0000000000006c0000000a406db00002202900000000000d000000000000500880000000000a5b0000000008800000000000000000006c000002200000000000001b000,
  0x18000618000018000600002988000618000018000600000618000618d000180006000506180006a4000018002200d00618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618000018002200000618000618000019400600000618000618d000180006000006180006a4000018000602900688000618d000180006000006180006180000a4000600002288000618000018000600000618000618000018d00601400618000618000018002200002988000618000019400600000618000618d000180006000506180006a4000018002202900618000618d000180006000029880006180000a4000600000618000618000018000600000618000618000018d02200002918000618d000180006000029880006180000a4000600000688000618d000180006000006180006a4000018002202900618000618d000180006000506880006180000a40006000006880006180000180006000506180022180000180006000006,
  0x2988000000000001b00000000000000000d000000000000500000000a5b00000002200d00000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000000000002200000000000000000001400000000000000000d000000000000000000000a406c000000002900088000000d0000000000006c0000000000000a400000000228800000000000000000006c000000000000000d00001400000000000000000002200002988000000000001b00000000000000000d000000000000500000000a5b6c000002202900000000000d000000000000029880000000000a5b00000000000000000000000000001b00000000001b01b00d02200002900000000d000000000000029880000000000a5b00000000088000000d0000000000006c0000000a406db00002202900000000000d000000000000500880000000000a5b0000000008800000000000000000006c000002200000000000001b000,
  0xa00000000000021021000000028000000028000000000000000000000000000021000000000000000000840000000000a00000000000000021000000000000000028840000000000028000000000021000000000000000000000000000000000a00000000000000000000000028a00000028000000000000000000000000000000000000000000000000028000000000000000000000000000000000000000000028000021000000000021000000000000000000028000000000000000000000a00000000000021021000000028a00000028000000000000000000000000000021000000000000000000868000000000a00000000000000021000000000000000028840000000000028000000000021000000000000000000000000000000000a00000000000000021000000000000000028840000000000000000000000000000000000000000000000028000000000000000000000000021000000028000000028840021000000028000000000000000000000028000000000000,
  0x1a000a0000000000002102100000002830000002800000001a680000000000000000021000300000000000000840000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000680000000a00000000000000000000000028a000000280000000000000000000000000000000003000000000000000280000004c000000000000000000000000000030000002800002100000000002100000000000000000002868000000000068001a000a00000000000021021000000028a0000002800000001a680000000000000000021000300000000000000868000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000000000680a000000000000000210000000003000000288400000004c000000000000000000000030000000000000002800001a680000000000000000021000000028300000028840021000000028000000000000000000000028000000000000,
  0x5000005a05005000005161021000005168305000028145005000005145005000005145021000305145005000005845005000005a050050000051450210000051453050000288450050000051680050000051610050003051454c5000005145005000005a05005000005145005000005168a050000281450050000051450050000051450050003051450050000051680050004c5145005000005145005000005145305000028145021000005145021000005145005000005168005000005145005000005a05005000005161021000005168a05000028145005000005145005000005145021000305145005000005868005000005a050050000051450210000051453050000288450050000051680050000051610050003051454c5000005145005000005a050050000051450210000051453050000288450050004c5145005000005145005000305145005000005168005000005145005000005145021000005168305000028845021000005168005000005145005000005168005000005145,
  0x1a000a0000000000002102100000002830000002800000001a680000000000000000021000300000000000000840000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000680000000a00000000000000000000000028a000000280000000000000000000000000000000003000000000000000280000004c000000000000000000000000000030000002800002100000000002100000000000000000002868000000000068001a000a00000000000021021000000028a0000002800000001a680000000000000000021000300000000000000868000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000000000680a000000000000000210000000003000000288400000004c000000000000000000000030000000000000002800001a680000000000000000021000000028300000028840021000000028000000000000000000000028000000000000,
  0x5000005a05005000005161021000005168305000028145005000005145005000005145021000305145005000005845005000005a05005000005145021000005145305000028845005000005168005000005161005000305145005000005145005000005a05005000005145005000005168a05000028145005000005145005000005145005000305145005000005168005000005145005000005145005000005145305000028145021000005145021000005145005000005168005000005145005000005a05005000005161021000005168a05000028145005000005145005000005145021000305145005000005868005000005a05005000005145021000005145305000028845005000005168005000005161005000305145005000005145005000005a05005000005145021000005145305000028845005000005145005000005145005000305145005000005168005000005145005000005145021000005168305000028845021000005168005000005145005000005168005000005145,
  0x1a000a0000000000002102100000002830000002800000001a680000000000000000021000300000000000000840000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000680000000a00000000000000000000000028a000000280000000000000000000000000000000003000000000000000280000004c000000000000000000000000000030000002800002100000000002100000000000000000002868000000000068001a000a00000000000021021000000028a0000002800000001a680000000000000000021000300000000000000868000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000000000680a000000000000000210000000003000000288400000004c000000000000000000000030000000000000002800001a680000000000000000021000000028300000028840021000000028000000000000000000000028000000000000,
  0x5000005a05005000005161021000005168305000028145005000005145005000005145021000305145005000005845005000005a050050000051450210000051453050000288450050000051680050000051610050003051454c5000005145005000005a05005000005145005000005168a050000281450050000051450050000051450050003051450050000051680050004c5145005000005145005000005145305000028145021000005145021000005145005000005168005000005145005000005a05005000005161021000005168a05000028145005000005145005000005145021000305145005000005868005000005a050050000051450210000051453050000288450050000051680050000051610050003051454c5000005145005000005a050050000051450210000051453050000288450050004c5145005000005145005000305145005000005168005000005145005000005145021000005168305000028845021000005168005000005145005000005168005000005145,
  0x1a000a0000000000002102100000002830000002800000001a680000000000000000021000300000000000000840000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000680000000a00000000000000000000000028a000000280000000000000000000000000000000003000000000000000280000004c000000000000000000000000000030000002800002100000000002100000000000000000002868000000000068001a000a00000000000021021000000028a0000002800000001a680000000000000000021000300000000000000868000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000000000680a000000000000000210000000003000000288400000004c000000000000000000000030000000000000002800001a680000000000000000021000000028300000028840021000000028000000000000000000000028000000000000,
  0x5000005a05005000005161021000005168005000028145005000005145005000005145021000005145005000005845005000005a05005000005145021000005145005000028845005000005168005000005161005000005145005000005145005000005a05005000005145005000005168a05000028145005000005145005000005145005000005145005000005168005000005145005000005145005000005145005000028145021000005145021000005145005000005168005000005145005000005a05005000005161021000005168a05000028145005000005145005000005145021000005145005000005868005000005a05005000005145021000005145005000028845005000005168005000005161005000005145005000005145005000005a05005000005145021000005145005000028845005000005145005000005145005000005145005000005168005000005145005000005145021000005168005000028845021000005168005000005145005000005168005000005145,
  0x1a000a0000000000002102100000002830000002800000001a680000000000000000021000300000000000000840000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000680000000a00000000000000000000000028a000000280000000000000000000000000000000003000000000000000280000004c000000000000000000000000000030000002800002100000000002100000000000000000002868000000000068001a000a00000000000021021000000028a0000002800000001a680000000000000000021000300000000000000868000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000000000680a000000000000000210000000003000000288400000004c000000000000000000000030000000000000002800001a680000000000000000021000000028300000028840021000000028000000000000000000000028000000000000,
  0x5000005a05005000005161021000005168305000028145005000005145005000005145021000305145005000005845005000005a050050000051450210000051453050000288450050000051680050000051610050003051454c5000005145005000005a05005000005145005000005168a050000281450050000051450050000051450050003051450050000051680050004c5145005000005145005000005145305000028145021000005145021000005145005000005168005000005145005000005a05005000005161021000005168a05000028145005000005145005000005145021000305145005000005868005000005a050050000051450210000051453050000288450050000051680050000051610050003051454c5000005145005000005a050050000051450210000051453050000288450050004c5145005000005145005000305145005000005168005000005145005000005145021000005168305000028845021000005168005000005145005000005168005000005145,
  0x1a000a0000000000002102100000002830000002800000001a680000000000000000021000300000000000000840000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000680000000a00000000000000000000000028a000000280000000000000000000000000000000003000000000000000280000004c000000000000000000000000000030000002800002100000000002100000000000000000002868000000000068001a000a00000000000021021000000028a0000002800000001a680000000000000000021000300000000000000868000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000000000680a000000000000000210000000003000000288400000004c000000000000000000000030000000000000002800001a680000000000000000021000000028300000028840021000000028000000000000000000000028000000000000,
  0x5000005a05005000005161021000005168305000028145005000005145005000005145021000305145005000005845005000005a05005000005145021000005145305000028845005000005168005000005161005000305145005000005145005000005a05005000005145005000005168a05000028145005000005145005000005145005000305145005000005168005000005145005000005145005000005145305000028145021000005145021000005145005000005168005000005145005000005a05005000005161021000005168a05000028145005000005145005000005145021000305145005000005868005000005a05005000005145021000005145305000028845005000005168005000005161005000305145005000005145005000005a05005000005145021000005145305000028845005000005145005000005145005000305145005000005168005000005145005000005145021000005168305000028845021000005168005000005145005000005168005000005145,
  0x1a000a0000000000002102100000002830000002800000001a680000000000000000021000300000000000000840000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000680000000a00000000000000000000000028a000000280000000000000000000000000000000003000000000000000280000004c000000000000000000000000000030000002800002100000000002100000000000000000002868000000000068001a000a00000000000021021000000028a0000002800000001a680000000000000000021000300000000000000868000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000000000680a000000000000000210000000003000000288400000004c000000000000000000000030000000000000002800001a680000000000000000021000000028300000028840021000000028000000000000000000000028000000000000,
  0x5000005a05005000005161021000005168305000028145005000005145005000005145021000305145005000005845005000005a050050000051450210000051453050000288450050000051680050000051610050003051454c5000005145005000005a05005000005145005000005168a050000281450050000051450050000051450050003051450050000051680050004c5145005000005145005000005145305000028145021000005145021000005145005000005168005000005145005000005a05005000005161021000005168a05000028145005000005145005000005145021000305145005000005868005000005a050050000051450210000051453050000288450050000051680050000051610050003051454c5000005145005000005a050050000051450210000051453050000288450050004c5145005000005145005000305145005000005168005000005145005000005145021000005168305000028845021000005168005000005145005000005168005000005145,
  0x1a000a0000000000002102100000002830000002800000001a680000000000000000021000300000000000000840000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000680000000a00000000000000000000000028a000000280000000000000000000000000000000003000000000000000280000004c000000000000000000000000000030000002800002100000000002100000000000000000002868000000000068001a000a00000000000021021000000028a0000002800000001a680000000000000000021000300000000000000868000000680a000000000000000210000000003000000288400000000000280000000000210000003000004c0000000000000000680a000000000000000210000000003000000288400000004c000000000000000000000030000000000000002800001a680000000000000000021000000028300000028840021000000028000000000000000000000028000000000000,
  0x6400270000000000000000008000000000009c00000000000000270000000000000000000000000000000000000000000000270000200000000000000000000000200000009c00000000000000000000270000000000000000000000000000008000000000000000009c00008000000000009c00000000000000000000000000000000000000000009c00000000000000270270000000000009c00000000000000000000000000000000000000000000270000008000000000000000000000008000270000000000009c00008000000000009c00000000000000270000000000000000000000000009c00000000000000000270000200000000000000000000000200000009c00000000000000000000270000000000000000000000000000000000270000200000000000000000000000200000000000000270270000000000000000000000000009c00000000000000000270000000000009c00000000000000200000009c0000800027000000000027000000000000000000000,
  0x64064b0270000000000000006408000000000009c000000000000b02700000000000000000001200000000000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000064080b0000000000000009c00008000000000009c000000000000b0000000000000000000000000000009c00000000000000270270000000000009c064000000000000000000000000000000000000000002700064080000000000001900000064080b0270000000000009c06408000000000009c000000000000b0270000000000000000000120000009c000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000000000b0270000200000000000000000000000200000000000000270270000000000000000000196400009c000000000000000b0270000000000009c00000000000000200000009c0640800027000000000027000640000640000000000,
  0x410000464b0271001041000041000048000041001049c000410000410b02710010410000410000411200410010410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000480b0041001041000049c00048000041001049c000410000410b0041001041000041000041000041009c41000041000041270271001041000049c000410000410010410000410000410000410010410002710000480000410010410000410000480b0271001041000049c00048000041001049c000410000410b0271001041000041000041120041009c410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000410b0271001201000041000041000041001201000041000041270271001041000041000041000041009c410000410000410b0271001041000049c00041000041001201000049c0004800027100104100027100004100004100104100,
  0x64064b0270000000000000006408000000000009c000000000000b02700000000000000000001200000000000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000064080b0000000000000009c00008000000000009c000000000000b0000000000000000000000000000009c00000000000000270270000000000009c064000000000000000000000000000000000000000002700064080000000000001900000064080b0270000000000009c06408000000000009c000000000000b0270000000000000000000120000009c000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000000000b0270000200000000000000000000000200000000000000270270000000000000000000196400009c000000000000000b0270000000000009c00000000000000200000009c0640800027000000000027000640000640000000000,
  0x410000464b0271001041000041000048000041001049c000410000410b02710010410000410000410000410010410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000480b0041001041000049c00048000041001049c000410000410b0041001041000041000041000041009c41000041000041270271001041000049c000410000410010410000410000410000410010410002710000480000410010410000410000480b0271001041000049c00048000041001049c000410000410b0271001041000041000041000041009c410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000410b0271001201000041000041000041001201000041000041270271001041000041000041000041009c410000410000410b0271001041000049c00041000041001201000049c0004800027100104100027100004100004100104100,
  0x64064b0270000000000000006408000000000009c000000000000b02700000000000000000001200000000000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000064080b0000000000000009c00008000000000009c000000000000b0000000000000000000000000000009c00000000000000270270000000000009c064000000000000000000000000000000000000000002700064080000000000001900000064080b0270000000000009c06408000000000009c000000000000b0270000000000000000000120000009c000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000000000b0270000200000000000000000000000200000000000000270270000000000000000000196400009c000000000000000b0270000000000009c00000000000000200000009c0640800027000000000027000640000640000000000,
  0x410000464b0271001041000041000048000041001049c000410000410b02710010410000410000411200410010410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000480b0041001041000049c00048000041001049c000410000410b0041001041000041000041000041009c41000041000041270271001041000049c000410000410010410000410000410000410010410002710000480000410010410000410000480b0271001041000049c00048000041001049c000410000410b0271001041000041000041120041009c410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000410b0271001201000041000041000041001201000041000041270271001041000041000041000041009c410000410000410b0271001041000049c00041000041001201000049c0004800027100104100027100004100004100104100,
  0x64064b0270000000000000006408000000000009c000000000000b02700000000000000000001200000000000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000064080b0000000000000009c00008000000000009c000000000000b0000000000000000000000000000009c00000000000000270270000000000009c064000000000000000000000000000000000000000002700064080000000000001900000064080b0270000000000009c06408000000000009c000000000000b0270000000000000000000120000009c000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000000000b0270000200000000000000000000000200000000000000270270000000000000000000196400009c000000000000000b0270000000000009c00000000000000200000009c0640800027000000000027000640000640000000000,
  0x41000046400271001041000041000048000041001049c00041000041000271001041000041000041000041001041000041000041000271001201000041000041000041001201000049c00041000041001041000271000041000041001041000041000048000041001041000049c00048000041001049c00041000041000041001041000041000041000041009c41000041000041270271001041000049c00041000041001041000041000041000041001041000271000048000041001041000041000048000271001041000049c00048000041001049c00041000041000271001041000041000041000041009c41000041000041000271001201000041000041000041001201000049c00041000041001041000271000041000041001041000041000041000271001201000041000041000041001201000041000041270271001041000041000041000041009c41000041000041000271001041000049c00041000041001201000049c0004800027100104100027100004100004100104100,
  0x64064b0270000000000000006408000000000009c000000000000b02700000000000000000001200000000000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000064080b0000000000000009c00008000000000009c000000000000b0000000000000000000000000000009c00000000000000270270000000000009c064000000000000000000000000000000000000000002700064080000000000001900000064080b0270000000000009c06408000000000009c000000000000b0270000000000000000000120000009c000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000000000b0270000200000000000000000000000200000000000000270270000000000000000000196400009c000000000000000b0270000000000009c00000000000000200000009c0640800027000000000027000640000640000000000,
  0x410000464b0271001041000041000048000041001049c000410000410b02710010410000410000411200410010410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000480b0041001041000049c00048000041001049c000410000410b0041001041000041000041000041009c41000041000041270271001041000049c000410000410010410000410000410000410010410002710000480000410010410000410000480b0271001041000049c00048000041001049c000410000410b0271001041000041000041120041009c410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000410b0271001201000041000041000041001201000041000041270271001041000041000041000041009c410000410000410b0271001041000049c00041000041001201000049c0004800027100104100027100004100004100104100,
  0x64064b0270000000000000006408000000000009c000000000000b02700000000000000000001200000000000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000064080b0000000000000009c00008000000000009c000000000000b0000000000000000000000000000009c00000000000000270270000000000009c064000000000000000000000000000000000000000002700064080000000000001900000064080b0270000000000009c06408000000000009c000000000000b0270000000000000000000120000009c000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000000000b0270000200000000000000000000000200000000000000270270000000000000000000196400009c000000000000000b0270000000000009c00000000000000200000009c0640800027000000000027000640000640000000000,
  0x410000464b0271001041000041000048000041001049c000410000410b02710010410000410000410000410010410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000480b0041001041000049c00048000041001049c000410000410b0041001041000041000041000041009c41000041000041270271001041000049c000410000410010410000410000410000410010410002710000480000410010410000410000480b0271001041000049c00048000041001049c000410000410b0271001041000041000041000041009c410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000410b0271001201000041000041000041001201000041000041270271001041000041000041000041009c410000410000410b0271001041000049c00041000041001201000049c0004800027100104100027100004100004100104100,
  0x64064b0270000000000000006408000000000009c000000000000b02700000000000000000001200000000000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000064080b0000000000000009c00008000000000009c000000000000b0000000000000000000000000000009c00000000000000270270000000000009c064000000000000000000000000000000000000000002700064080000000000001900000064080b0270000000000009c06408000000000009c000000000000b0270000000000000000000120000009c000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000000000b0270000200000000000000000000000200000000000000270270000000000000000000196400009c000000000000000b0270000000000009c00000000000000200000009c0640800027000000000027000640000640000000000,
  0x410000464b0271001041000041000048000041001049c000410000410b02710010410000410000411200410010410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000480b0041001041000049c00048000041001049c000410000410b0041001041000041000041000041009c41000041000041270271001041000049c000410000410010410000410000410000410010410002710000480000410010410000410000480b0271001041000049c00048000041001049c000410000410b0271001041000041000041120041009c410000410000410b0271001201000041000041000041001201000049c000410000410010410002710000410000410010410000410000410b0271001201000041000041000041001201000041000041270271001041000041000041000041009c410000410000410b0271001041000049c00041000041001201000049c0004800027100104100027100004100004100104100,
  0x64064b0270000000000000006408000000000009c000000000000b02700000000000000000001200000000000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000064080b0000000000000009c00008000000000009c000000000000b0000000000000000000000000000009c00000000000000270270000000000009c064000000000000000000000000000000000000000002700064080000000000001900000064080b0270000000000009c06408000000000009c000000000000b0270000000000000000000120000009c000000000000000b0270000200000000000000000000000200000009c064000000000000000002700000001900000000000000000000000b0270000200000000000000000000000200000000000000270270000000000000000000196400009c000000000000000b0270000000000009c00000000000000200000009c0640800027000000000027000640000640000000000,
  0x9800000000000000000000000009800000000260000000000000000000000000000007c00000000000000000000000000000000007c00000000000000009800000000000000000000000000000000000000006000000000000000000000000009ad0000000000000000000000000000000000000000000000000000000000000000000000009800007c00000000000009ad0000000000000000000000260000007c00000000000000000000000000000000006000000000000000000000000009ad0000000000000000000000009800000000260000000000000000000000000000007c00000000000000000000000000000000007c00000000000000009800000000000000000000000000000000000000007c00000000000000000000000000000000000000000000000000009800000000000000000000000000000000000000000000009800007c0000000000000000000000000000000000000000980000600000000000000026000000,
  0x1800000000000a01800000000000060000098a00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a00001800000000000060000a0000000000000000000009ad00000000000000000000000a00000000000a00000000000000000000000000000000000a9800007c00000000000009ad0000000000000000000000260000007c000a00060000000a00000000001800000060000a0180000000000006000009ad00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a0000180000110000007c000a01800000000000000000000a00000000000000000000000a98000000000a00000000000000000000001800000000000a9800007c000000060000000a00000000000000060000000a98000060000a000600000026000000,
  0xc00c00c00000c00ca0c00000c00c00c00000c098a0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca0c00000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c09ad0c00000c00c00c00000c00e60c00007c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00ca9800000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c00ca0c00000c00c00c00000c00ca9800006000ca0c00000c00e60c0000,
  0x1800000000000a01800000000000060000098a00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a00001800000000000060000a0000000000000000000009ad00000000000000000000000a00000000000a00000000000000000000000000000000000a9800007c00000000000009ad0000000000000000000000260000007c000a00060000000a00000000001800000060000a0180000000000006000009ad00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a0000180000110000007c000a01800000000000000000000a00000000000000000000000a98000000000a00000000000000000000001800000000000a9800007c000000060000000a00000000000000060000000a98000060000a000600000026000000,
  0xc00c00c00000c00ca0c00000c00c00c00000c098a0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00c00c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca0c00000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c09ad0c00000c00c00c00000c00e60c00007c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00c00c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00c00c00007c00ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00ca9800000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c00ca0c00000c00c00c00000c00ca9800006000ca0c00000c00e60c0000,
  0x1800000000000a01800000000000060000098a00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a00001800000000000060000a0000000000000000000009ad00000000000000000000000a00000000000a00000000000000000000000000000000000a9800007c00000000000009ad0000000000000000000000260000007c000a00060000000a00000000001800000060000a0180000000000006000009ad00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a0000180000110000007c000a01800000000000000000000a00000000000000000000000a98000000000a00000000000000000000001800000000000a9800007c000000060000000a00000000000000060000000a98000060000a000600000026000000,
  0xc00c00c00000c00ca0c00000c00c00c00000c098a0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca0c00000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c09ad0c00000c00c00c00000c00e60c00007c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00ca9800000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c00ca0c00000c00c00c00000c00ca9800006000ca0c00000c00e60c0000,
  0x1800000000000a01800000000000060000098a00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a00001800000000000060000a0000000000000000000009ad00000000000000000000000a00000000000a00000000000000000000000000000000000a9800007c00000000000009ad0000000000000000000000260000007c000a00060000000a00000000001800000060000a0180000000000006000009ad00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a0000180000110000007c000a01800000000000000000000a00000000000000000000000a98000000000a00000000000000000000001800000000000a9800007c000000060000000a00000000000000060000000a98000060000a000600000026000000,
  0xc00c00c00000c00c00c00000c00c00c00000c09800c00000c00c00c00000c00c09800000c00e60c00000c00c00c00000c00c00c00007c00c00c00000c00c00c00000c00c00c00007c00c00c00000c00c09800000c00c00c00000c00c00c00000c00c00c00006000c00c00000c00c00c00000c09ad0c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c09800007c00c00c00000c09ad0c00000c00c00c00000c00e60c00007c00c00c00000c00c00c00000c00c00c00006000c00c00000c00c00c00000c09ad0c00000c00c00c00000c00c09800000c00e60c00000c00c00c00000c00c00c00007c00c00c00000c00c00c00000c00c00c00007c00c00c00000c00c09800000c00c00c00000c00c00c00000c00c00c00007c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c09800000c00c00c00000c00c00c00000c00c00c00000c00c09800007c00c00c00000c00c00c00000c00c00c00000c00c09800006000c00c00000c00e60c0000,
  0x1800000000000a01800000000000060000098a00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a00001800000000000060000a0000000000000000000009ad00000000000000000000000a00000000000a00000000000000000000000000000000000a9800007c00000000000009ad0000000000000000000000260000007c000a00060000000a00000000001800000060000a0180000000000006000009ad00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a0000180000110000007c000a01800000000000000000000a00000000000000000000000a98000000000a00000000000000000000001800000000000a9800007c000000060000000a00000000000000060000000a98000060000a000600000026000000,
  0xc00c00c00000c00ca0c00000c00c00c00000c098a0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca0c00000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c09ad0c00000c00c00c00000c00e60c00007c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00ca9800000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c00ca0c00000c00c00c00000c00ca9800006000ca0c00000c00e60c0000,
  0x1800000000000a01800000000000060000098a00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a00001800000000000060000a0000000000000000000009ad00000000000000000000000a00000000000a00000000000000000000000000000000000a9800007c00000000000009ad0000000000000000000000260000007c000a00060000000a00000000001800000060000a0180000000000006000009ad00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a0000180000110000007c000a01800000000000000000000a00000000000000000000000a98000000000a00000000000000000000001800000000000a9800007c000000060000000a00000000000000060000000a98000060000a000600000026000000,
  0xc00c00c00000c00ca0c00000c00c00c00000c098a0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00c00c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca0c00000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c09ad0c00000c00c00c00000c00e60c00007c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00c00c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00c00c00007c00ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00ca9800000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c00ca0c00000c00c00c00000c00ca9800006000ca0c00000c00e60c0000,
  0x1800000000000a01800000000000060000098a00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a00001800000000000060000a0000000000000000000009ad00000000000000000000000a00000000000a00000000000000000000000000000000000a9800007c00000000000009ad0000000000000000000000260000007c000a00060000000a00000000001800000060000a0180000000000006000009ad00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a0000180000110000007c000a01800000000000000000000a00000000000000000000000a98000000000a00000000000000000000001800000000000a9800007c000000060000000a00000000000000060000000a98000060000a000600000026000000,
  0xc00c00c00000c00ca0c00000c00c00c00000c098a0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca0c00000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c09ad0c00000c00c00c00000c00e60c00007c00ca0c00000c00ca0c00000c00c00c00006000ca0c00000c00c00c00000c09ad0c00000c00c00c00000c00ca9800000c00e60c00000c00c00c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00007c00c00c00000c00ca9800000c00ca0c00000c00ca0c00000c00d10c00007c00ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00ca9800000c00ca0c00000c00c00c00000c00c00c00000c00ca9800007c00c00c00000c00ca0c00000c00c00c00000c00ca9800006000ca0c00000c00e60c0000,
  0x1800000000000a01800000000000060000098a00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a00001800000000000060000a0000000000000000000009ad00000000000000000000000a00000000000a00000000000000000000000000000000000a9800007c00000000000009ad0000000000000000000000260000007c000a00060000000a00000000001800000060000a0180000000000006000009ad00000000001800000000000a9800000000260000000000000000000000110000007c000a01800000000000000000000a0000007c000000060000000a98000000000a00000000000a0000180000110000007c000a01800000000000000000000a00000000000000000000000a98000000000a00000000000000000000001800000000000a9800007c000000060000000a00000000000000060000000a98000060000a000600000026000000,
  0xb0002500000000000000000000000000000000000000001e000025000000000000000000000000000000000000000000000000000000940000000000000000000000000b0000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000b00025000000000000000000000000000000000000000000000000000000000000b00017940000000000000000000000b0002500000000000000000000000000000000000000001e000025000000000000000000000000000000000000000000000000000000940000000000000000000000000b0000000000000000000000000000001e000000000000000000000000000000000000940000000000000000000000000b00000000b00025000000000000000000000000000000000000000000000025000000000000000000000000000000000b00000000000000000000000000000000000000000000000000000000,
  0xb0002500000024000024000000000000000000024000001e240025400000240000240000240000000000000240000000240000000000940000240000000000000000000b000000000170005c000024000024001e2400000000004000000000002400005c000024000024000001700000000000024000001e2400004000002400002400002400000000000002400005c0b000254000002400002400000000005c0000000240000000000000000000240000b00017940000000000000000000000b000255c000024000024000001700000000000024000001e2400254000002400002400002400000000000002400005c0240000000000940000240000000000000000000b000000000170005c000024000024001e240000000000400000000000240000000000940000240000000000000000000b00000000b000254000002400002400002400000000005c02400005c0240025400000240000240000017000000000000b000000000170000000002400002400002400005c00005c0000000000,
  0xb0002500000224000224000200000200000200024200001e240025400002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e24000200000240000200000224000200000224000224000200000200000200024200001e240002400002240002240002240002000002000242000002b00025400002240002240002000002000002000242000002000002000002240002b00017940002000002000002000002b0002500000224000224000200000200000200024200001e240025400002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e240002000002400002000002240002000002940002240002000002000002000b02000002b00025400002240002240002240002000002000242000002240025400002240002240002000002000002000b02000002000002000002240002240002240002000002000002000002,
  0xb0002500000024000024000000000000000000024000001e240025400000240000240000240000000000000240000000240000000000940000240000000000000000000b000000000170005c000024000024001e2400000000004000000000002400005c000024000024000001700000000000024000001e2400004000002400002400002400000000000002400005c0b000254000002400002400000000005c0000000240000000000000000000240000b00017940000000000000000000000b000255c000024000024000001700000000000024000001e2400254000002400002400002400000000000002400005c0240000000000940000240000000000000000000b000000000170005c000024000024001e240000000000400000000000240000000000940000240000000000000000000b00000000b000254000002400002400002400000000005c02400005c0240025400000240000240000017000000000000b000000000170000000002400002400002400005c00005c0000000000,
  0xb0002500000224000224000200000200000200024200001e240025000002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e24000200000200000200000224000200000224000224000200000200000200024200001e240002000002240002240002240002000002000242000002b00025000002240002240002000002000002000242000002000002000002240002b00017940002000002000002000002b0002500000224000224000200000200000200024200001e240025000002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e240002000002000002000002240002000002940002240002000002000002000b02000002b00025000002240002240002240002000002000242000002240025000002240002240002000002000002000b02000002000002000002240002240002240002000002000002000002,
  0xb0002500000024000024000000000000000000024000001e240025400000240000240000240000000000000240000000240000000000940000240000000000000000000b000000000170005c000024000024001e2400000000004000000000002400005c000024000024000001700000000000024000001e2400004000002400002400002400000000000002400005c0b000254000002400002400000000005c0000000240000000000000000000240000b00017940000000000000000000000b000255c000024000024000001700000000000024000001e2400254000002400002400002400000000000002400005c0240000000000940000240000000000000000000b000000000170005c000024000024001e240000000000400000000000240000000000940000240000000000000000000b00000000b000254000002400002400002400000000005c02400005c0240025400000240000240000017000000000000b000000000170000000002400002400002400005c00005c0000000000,
  0xb0002500000224000224000200000200000200024200001e240025400002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e24000200000240000200000224000200000224000224000200000200000200024200001e240002400002240002240002240002000002000242000002b00025400002240002240002000002000002000242000002000002000002240002b00017940002000002000002000002b0002500000224000224000200000200000200024200001e240025400002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e240002000002400002000002240002000002940002240002000002000002000b02000002b00025400002240002240002240002000002000242000002240025400002240002240002000002000002000b02000002000002000002240002240002240002000002000002000002,
  0xb0002500000024000024000000000000000000024000001e240025400000240000240000240000000000000240000000240000000000940000240000000000000000000b000000000170005c000024000024001e2400000000004000000000002400005c000024000024000001700000000000024000001e2400004000002400002400002400000000000002400005c0b000254000002400002400000000005c0000000240000000000000000000240000b00017940000000000000000000000b000255c000024000024000001700000000000024000001e2400254000002400002400002400000000000002400005c0240000000000940000240000000000000000000b000000000170005c000024000024001e240000000000400000000000240000000000940000240000000000000000000b00000000b000254000002400002400002400000000005c02400005c0240025400000240000240000017000000000000b000000000170000000002400002400002400005c00005c0000000000,
  0xb0002500000200000200000200000200000200000200001e000025000002000002000002000002000002000002000002000002000002940002000002000002000002000b0200000200000200000200000200001e00000200000200000200000200000200000200000200000200000200000200000200001e000002000002000002000002000002000002000002000002b00025000002000002000002000002000002000002000002000002000002000002b00017940002000002000002000002b0002500000200000200000200000200000200000200001e000025000002000002000002000002000002000002000002000002000002940002000002000002000002000b0200000200000200000200000200001e000002000002000002000002000002000002940002000002000002000002000b02000002b00025000002000002000002000002000002000002000002000025000002000002000002000002000002000b02000002000002000002000002000002000002000002000002000002,
  0xb0002500000024000024000000000000000000024000001e240025400000240000240000240000000000000240000000240000000000940000240000000000000000000b000000000170005c000024000024001e2400000000004000000000002400005c000024000024000001700000000000024000001e2400004000002400002400002400000000000002400005c0b000254000002400002400000000005c0000000240000000000000000000240000b00017940000000000000000000000b000255c000024000024000001700000000000024000001e2400254000002400002400002400000000000002400005c0240000000000940000240000000000000000000b000000000170005c000024000024001e240000000000400000000000240000000000940000240000000000000000000b00000000b000254000002400002400002400000000005c02400005c0240025400000240000240000017000000000000b000000000170000000002400002400002400005c00005c0000000000,
  0xb0002500000224000224000200000200000200024200001e240025400002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e24000200000240000200000224000200000224000224000200000200000200024200001e240002400002240002240002240002000002000242000002b00025400002240002240002000002000002000242000002000002000002240002b00017940002000002000002000002b0002500000224000224000200000200000200024200001e240025400002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e240002000002400002000002240002000002940002240002000002000002000b02000002b00025400002240002240002240002000002000242000002240025400002240002240002000002000002000b02000002000002000002240002240002240002000002000002000002,
  0xb0002500000024000024000000000000000000024000001e240025400000240000240000240000000000000240000000240000000000940000240000000000000000000b000000000170005c000024000024001e2400000000004000000000002400005c000024000024000001700000000000024000001e2400004000002400002400002400000000000002400005c0b000254000002400002400000000005c0000000240000000000000000000240000b00017940000000000000000000000b000255c000024000024000001700000000000024000001e2400254000002400002400002400000000000002400005c0240000000000940000240000000000000000000b000000000170005c000024000024001e240000000000400000000000240000000000940000240000000000000000000b00000000b000254000002400002400002400000000005c02400005c0240025400000240000240000017000000000000b000000000170000000002400002400002400005c00005c0000000000,
  0xb0002500000224000224000200000200000200024200001e240025000002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e24000200000200000200000224000200000224000224000200000200000200024200001e240002000002240002240002240002000002000242000002b00025000002240002240002000002000002000242000002000002000002240002b00017940002000002000002000002b0002500000224000224000200000200000200024200001e240025000002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e240002000002000002000002240002000002940002240002000002000002000b02000002b00025000002240002240002240002000002000242000002240025000002240002240002000002000002000b02000002000002000002240002240002240002000002000002000002,
  0xb0002500000024000024000000000000000000024000001e240025400000240000240000240000000000000240000000240000000000940000240000000000000000000b000000000170005c000024000024001e2400000000004000000000002400005c000024000024000001700000000000024000001e2400004000002400002400002400000000000002400005c0b000254000002400002400000000005c0000000240000000000000000000240000b00017940000000000000000000000b000255c000024000024000001700000000000024000001e2400254000002400002400002400000000000002400005c0240000000000940000240000000000000000000b000000000170005c000024000024001e240000000000400000000000240000000000940000240000000000000000000b00000000b000254000002400002400002400000000005c02400005c0240025400000240000240000017000000000000b000000000170000000002400002400002400005c00005c0000000000,
  0xb0002500000224000224000200000200000200024200001e240025400002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e24000200000240000200000224000200000224000224000200000200000200024200001e240002400002240002240002240002000002000242000002b00025400002240002240002000002000002000242000002000002000002240002b00017940002000002000002000002b0002500000224000224000200000200000200024200001e240025400002240002240002240002000002000242000002240002000002940002240002000002000002000b0200000200000200000224000224001e240002000002400002000002240002000002940002240002000002000002000b02000002b00025400002240002240002240002000002000242000002240025400002240002240002000002000002000b02000002000002000002240002240002240002000002000002000002,
  0xb0002500000024000024000000000000000000024000001e240025400000240000240000240000000000000240000000240000000000940000240000000000000000000b000000000170005c000024000024001e2400000000004000000000002400005c000024000024000001700000000000024000001e2400004000002400002400002400000000000002400005c0b000254000002400002400000000005c0000000240000000000000000000240000b00017940000000000000000000000b000255c000024000024000001700000000000024000001e2400254000002400002400002400000000000002400005c0240000000000940000240000000000000000000b000000000170005c000024000024001e240000000000400000000000240000000000940000240000000000000000000b00000000b000254000002400002400002400000000005c02400005c0240025400000240000240000017000000000000b000000000170000000002400002400002400005c00005c0000000000
]

/-! ### States, the step and the check -/

/-- The block `0001011`, letter `p` at phase `p`. -/
def w0001011 : List Bool := [false, false, false, true, false, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `6 w .. 6 w + 5` of table
`16 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (16 * p + s) 0 >>> (6 * w)) % 64

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `101`, `1001`, `10001`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 8 == 5) ||
    ((2 * s + b.toNat) % 16 == 9) ||
    ((2 * s + b.toNat) % 32 == 17)

/-- The last 4 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 16 else s

/-- The window of columns 1..9 after a step from phase `p`, with column 10 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 9 (w0001011.getD p false) z w

/-- The certificate at one state: ranks are at most 45; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 7) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 7) (sNext p s w) (wNext p w true)
  decide (r ≤ 45) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 512

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 16 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 16 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 16 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 16 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 16 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 16 = true := by decide +kernel
theorem ok_6 : allBelowT (partOK 6) 16 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 7 → allBelowT (partOK p) 16 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | 6, _ => ok_6
  | p + 7, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 7) (hs : s < 16) (hw : w < 2 ^ 9) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 9 = 512 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 45 ∧
      (rk p s w = 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `0001011` read from phase `ph`: letter `(t + ph) % 7` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w0001011.getD ((t + ph) % 7) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..9` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 9
  | t + 1 => stripStep 9 (F t 0) (F t 10) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 9 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 9).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last four readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 7) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 16
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 16
    unfold sNext
    cases ((t + ph) % 7 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 16

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 7) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 10) := by
  show stripStep 9 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `45 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 45 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 10)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 7 = ((t + ph) % 7 + 1) % 7 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 45 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 45 ≤ t) (hp : (t + ph) % 7 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 7 = 0) :
    suf ph (drv (ctr ph) R) (t + 7) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 7) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  have h7 : suf ph (drv (ctr ph) R) (t + 7) = suf ph (drv (ctr ph) R) (t + 6) := by
    show sNext ((t + 6 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 6)) (win (drv (ctr ph) R) (t + 6)) = _
    exact sNext_ne (by omega)
  rw [h7, h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_101 : ∀ s, s < 16 → badB (push (push s true) false) true = true := by decide +kernel
theorem bad_1001 : ∀ s, s < 16 → badB (push (push (push s true) false) false) true = true := by decide +kernel
theorem bad_10001 : ∀ s, s < 16 → badB (push (push (push (push s true) false) false) false) true = true
    := by decide +kernel

end ReadingWords.B0001011

open ReadingWords.B0001011

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `101`.** At the first white steps, column 1 never reads `101` with the first reading at time `31` or
later. -/
theorem no_101_time_0001011 (u : Nat) (hu : 31 ≤ u) (hp : (u + ph) % 7 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 7) 1 = false ∧ drv (ctr ph) R (u + 14) 1 = true) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 14 = u + 7 + 7 by omega] at h2
  have hb := no_bad R ph (u + 7 + 7) (by omega) (by omega)
  rw [suf_period R ph (u + 7) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_101 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `1001`.** At the first white steps, column 1 never reads `1001` with the first reading at time `24` or
later. -/
theorem no_1001_time_0001011 (u : Nat) (hu : 24 ≤ u) (hp : (u + ph) % 7 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 7) 1 = false ∧ drv (ctr ph) R (u + 14) 1 = false ∧
      drv (ctr ph) R (u + 21) 1 = true) := by
  rintro ⟨h0, h1, h2, h3⟩
  rw [show u + 14 = u + 7 + 7 by omega] at h2
  rw [show u + 21 = u + 7 + 7 + 7 by omega] at h3
  have hb := no_bad R ph (u + 7 + 7 + 7) (by omega) (by omega)
  rw [suf_period R ph (u + 7 + 7) (by omega), suf_period R ph (u + 7) (by omega), suf_period R ph u hp, h0, h1, h2,
    h3] at hb
  rw [bad_1001 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `10001`.** At the first white steps, column 1 never reads `10001` with the first reading at time `17` or
later. -/
theorem no_10001_time_0001011 (u : Nat) (hu : 17 ≤ u) (hp : (u + ph) % 7 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 7) 1 = false ∧ drv (ctr ph) R (u + 14) 1 = false ∧
      drv (ctr ph) R (u + 21) 1 = false ∧ drv (ctr ph) R (u + 28) 1 = true) := by
  rintro ⟨h0, h1, h2, h3, h4⟩
  rw [show u + 14 = u + 7 + 7 by omega] at h2
  rw [show u + 21 = u + 7 + 7 + 7 by omega] at h3
  rw [show u + 28 = u + 7 + 7 + 7 + 7 by omega] at h4
  have hb := no_bad R ph (u + 7 + 7 + 7 + 7) (by omega) (by omega)
  rw [suf_period R ph (u + 7 + 7 + 7) (by omega), suf_period R ph (u + 7 + 7) (by omega),
    suf_period R ph (u + 7) (by omega), suf_period R ph u hp, h0, h1, h2, h3, h4] at hb
  rw [bad_10001 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B0001011

/-- A sequence of bits has none of the factors `101`, `1001`, `10001` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = false ∧ b (i + 3) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = false ∧ b (i + 3) = false ∧ b (i + 4) = true)

/-- Column 1 of the right half driven by `0001011` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 7 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (7 * i + (7 - ph % 7) % 7) 1

end ReadingWords.B0001011

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`101`, `1001`, `10001` from the 5th on. -/
theorem readings_0001011 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 5 := by
  intro i hi
  have hp : (7 * i + (7 - ph % 7) % 7 + ph) % 7 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 7) 1 := by
    unfold reading; rw [show 7 * (i + 1) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 7 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 14) 1 := by
    unfold reading; rw [show 7 * (i + 2) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 14 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 21) 1 := by
    unfold reading; rw [show 7 * (i + 3) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 21 by omega]
  have e4 : reading R ph (i + 4) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 28) 1 := by
    unfold reading; rw [show 7 * (i + 4) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 28 by omega]
  rw [e1, e2, e3, e4]
  exact ⟨no_101_time_0001011 R ph _ (by omega) hp, no_1001_time_0001011 R ph _ (by omega) hp,
    no_10001_time_0001011 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `0001011` -/

namespace ReadingWords.B0001011

/-- From time `T` on, a row whose center column repeats `0001011` from `T` has the right half driven by `0001011` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0001011.getD ((t - T) % 7) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w0001011.getD ((0 + 0) % 7) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w0001011.getD ((t + 1 + 0) % 7) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B0001011

/-- **Readings of every row.** If the center column of a row repeats `0001011` from time `T` (letter
`(t - T) % 7` at time `t`), then column 1 at the times `T + 7 i` avoids `101`, `1001`, `10001` from `i = 5` on. -/
theorem readings_0001011_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0001011.getD ((t - T) % 7) false) :
    Avoids (fun i => evolve init (T + 7 * i) 1) 5 := by
  have e : (fun i => evolve init (T + 7 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 7 * i = T + (7 * i + (7 - 0 % 7) % 7) by omega]
    exact evolve_eq_drv init T h (7 * i + (7 - 0 % 7) % 7) 1
  rw [e]
  exact readings_0001011 _ 0

end B0001011

/-! ## Block `0011011` -/

section B0011011

/-! The certificate and the helpers live in `ReadingWords.B0011011`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B0011011

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `16 * p + s` packs the rank of window `w` in bits `6 w .. 6 w + 5`. -/
def rankTabs : List Nat := [
  0x80160010013cf0080163eb0080160013c13c101600100f0080160010013cf00800100f3d60083c100100100801d01601d0163d60013c801d0013f20080160013c13c100f00159d0080160013c13c80080013dd3cf0083c13c100101d0010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c10010010080010160080163dd0163cf0080010240080160013c13c10080010080080160013c13d60080010243c801d0010013d60080010010080160010163cf0080163eb0080010010013c100f00100f0080163dd0013cf00801600f3cf01d3c100100100801d01601d0163d60013c801d0013f20080160013c13c100f0015880080160013c13dd0080013d63cf0083c13c13c100800100101d0163d60013c801d0013f90080160013c13c100f0015880080163dd0163cf0080010243c80083c10010010080160160080160010013cf00800100f0080160013c13c10080010080080160010013cf00801600f3c801d0013c100101d0010010080160010163cf0080163eb0080160013c13c101600100f0080163dd0013cf00801600f3d601d3c100100100801d01601d0163d60013c801d0013f20080160013c13c100f00159d0080160013c13dd0080013dd3cf0083c13c13c101d0010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c10010010080010160080163dd0163cf0080010240080160013c13c10080010080080160013c13d60080010243c801d0010013d60080010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c100100100800101601d0163d60013c801d0013f90080160013c13c100f0015880080160013c13dd0080013e43cf0083c13c13dd01d00100101d0163d60013c801d0013f20080160013c13c100f00159d0080163c10163cf0080010243dd0083c10010010080160160080163dd0013cf00801600f0080160013c13c100f00159d0080160013c13cf0080010243cf0080013c1001008001001,
  0x20020020f00000022b00000020020020001600000f00000020020020f00000020f21600020020020000001d00001d00020020020001d00023200000020020020000f00059d00000020020020000000021d20f00020020020001d00000000000020020020001d00022b00000020020020000000000f00000020020020f00000020f20000020020020000000000000000021d20020f00000022400000020020020000000000000000020020021600000022420001d20020020000000000000000020020020f00000022b00000020020020000f00000f00000021d20020f00000020f20f01d20020020000001d00001d00020020020001d00023200000020020020000f00058000000020020021d00000021620f00020020020000000000001d00020020020001d00023900000020020020000f00058000000021d20020f00000022420000020020020000000000000000020020020f00000020f00000020020020000000000000000020020020f00000020f20001d20020020001d00000000000020020020f00000022b00000020020020001600000f00000021d20020f00000020f21601d20020020000001d00001d00020020020001d00023200000020020020000f00059d00000020020021d00000021d20f00020020020001d00000000000020020020001d00022b00000020020020000000000f00000020020020f00000020f20000020020020000000000000000021d20020f00000022400000020020020000000000000000020020021600000022420001d20020020000000000000000020020020001d00022b00000020020020000000000f00000020020020f00000020f20000020020020000000000001d00020020020001d00023900000020020020000f00058000000020020021d00000022420f00020020021d01d00000001d00020020020001d00023200000020020020000f00059d00000020020020f00000022421d00020020020000000000000000021d20020f00000020f00000020020020000f00059d00000020020020f00000022420f000200200200000000000,
  0x801600000000f00801602b00801600000000001600000f00801600000000f00800000f01600800000000000801d01601d01601600000801d00003200801600000000000f00059d00801600000000800800001d00f00800000000001d00000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001600801601d01600f00800002400801600000000000800000800801600000001600800002400801d00000001600800000000801600001600f00801602b00800000000000000f00000f00801601d00000f00801600f00f01d00000000000801d01601d01601600000801d00003200801600000000000f00058800801600000001d00800001600f00800000000000800000001d01601600000801d00003900801600000000000f00058800801601d01600f00800002400800800000000000801601600801600000000f00800000f00801600000000000800000800801600000000f00801600f00801d00000000001d00000000801600001600f00801602b00801600000000001600000f00801601d00000f00801600f01601d00000000000801d01601d01601600000801d00003200801600000000000f00059d00801600000001d00800001d00f00800000000001d00000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001600801601d01600f00800002400801600000000000800000800801600000001600800002400801d00000001600800000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001601d01601600000801d00003900801600000000000f00058800801600000001d00800002400f00800000001d01d00000001d01601600000801d00003200801600000000000f00059d00801600001600f00800002401d00800000000000801601600801601d00000f00801600f00801600000000000f00059d00801600000000f00800002400f008000000000008000000,
  0x4004004004004f04004006b04004004004004005604004f04004004004004f04004004f05604004004004004005d04005d04004004004005d04007204004004004004004f04059d04004004004004004004005d04f04004004004005d04004004004004004004005d04006b04004004004004004004004f04004004004004f04004004f04004004004004004004004004004005d04004f04004006404004004004004004004004004004004004005604004006404005d04004004004004004004004004004004f04004006b04004004004004004f04004f04004005d04004f04004004f04f05d04004004004005d04005d04004004004005d04007204004004004004004f04058004004004004005d04004005604f04004004004004004004005d04004004004005d04007904004004004004004f04058004004005d04004f04004006404004004004004004004004004004004004004f04004004f04004004004004004004004004004004004004f04004004f04005d04004004005d04004004004004004004f04004006b04004004004004005604004f04004005d04004f04004004f05605d04004004004005d04005d04004004004005d04007204004004004004004f04059d04004004004005d04004005d04f04004004004005d04004004004004004004005d04006b04004004004004004004004f04004004004004f04004004f04004004004004004004004004004005d04004f04004006404004004004004004004004004004004004005604004006404005d04004004004004004004004004004004005d04006b04004004004004004004004f04004004004004f04004004f04004004004004004004004005d04004004004005d04007904004004004004004f04058004004004004005d04004006404f04004004005d05d04004005d04004004004005d04007204004004004004004f04059d04004004004004f04004006405d04004004004004004004004004005d04004f04004004f04004004004004004f04059d04004004004004f04004006404f040040040040040040040,
  0x80160010013cf0080163eb0080160013c13c101600100f0080160010013cf00800100f3d60083c100100100801d01601d0163d60013c801d0013f20080160013c13c100f00159d0080160013c13c80080013dd3cf0083c13c100101d0010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c10010010080010160080163dd0163cf0080010240080160013c13c10080010080080160013c13d60080010243c801d0010013d60080010010080160010163cf0080163eb0080010010013c100f00100f0080163dd0013cf00801600f3cf01d3c100100100801d01601d0163d60013c801d0013f20080160013c13c100f0015880080160013c13dd0080013d63cf0083c13c13c100800100101d0163d60013c801d0013f90080160013c13c100f0015880080163dd0163cf0080010243c80083c10010010080160160080160010013cf00800100f0080160013c13c10080010080080160010013cf00801600f3c801d0013c100101d0010010080160010163cf0080163eb0080160013c13c101600100f0080163dd0013cf00801600f3d601d3c100100100801d01601d0163d60013c801d0013f20080160013c13c100f00159d0080160013c13dd0080013dd3cf0083c13c13c101d0010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c10010010080010160080163dd0163cf0080010240080160013c13c10080010080080160013c13d60080010243c801d0010013d60080010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c100100100800101601d0163d60013c801d0013f90080160013c13c100f0015880080160013c13dd0080013e43cf0083c13c13dd01d00100101d0163d60013c801d0013f20080160013c13c100f00159d0080163c10163cf0080010243dd0083c10010010080160160080163dd0013cf00801600f0080160013c13c100f00159d0080160013c13cf0080010243cf0080013c1001008001001,
  0xf00000002b00000000000000001600000f00000000000000f00000000f01600000000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000000000000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000f00000002b00000000000000000f00000f00000001d00000f00000000f00f01d00000000000001d00001d00000000000001d00003200000000000000000f00058000000000000001d00000001600f00000000000000000000001d00000000000001d00003900000000000000000f00058000000001d00000f00000002400000000000000000000000000000000000000f00000000f00000000000000000000000000000000000000f00000000f00001d00000000001d00000000000000000000f00000002b00000000000000001600000f00000001d00000f00000000f01601d00000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000001d00000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000001d00000000000001d00003900000000000000000f00058000000000000001d00000002400f00000000001d01d00000001d00000000000001d00003200000000000000000f00059d00000000000000f00000002401d00000000000000000000000000001d00000f00000000f00000000000000000f00059d00000000000000f00000002400f000000000000000000000,
  0x801600000000f00801602b00801600000000001600000f00801600000000f00800000f01600800000000000801d01601d01601600000801d00003200801600000000000f00059d00801600000000800800001d00f00800000000001d00000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001600801601d01600f00800002400801600000000000800000800801600000001600800002400801d00000001600800000000801600001600f00801602b00800000000000000f00000f00801601d00000f00801600f00f01d00000000000801d01601d01601600000801d00003200801600000000000f00058800801600000001d00800001600f00800000000000800000001d01601600000801d00003900801600000000000f00058800801601d01600f00800002400800800000000000801601600801600000000f00800000f00801600000000000800000800801600000000f00801600f00801d00000000001d00000000801600001600f00801602b00801600000000001600000f00801601d00000f00801600f01601d00000000000801d01601d01601600000801d00003200801600000000000f00059d00801600000001d00800001d00f00800000000001d00000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001600801601d01600f00800002400801600000000000800000800801600000001600800002400801d00000001600800000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001601d01601600000801d00003900801600000000000f00058800801600000001d00800002400f00800000001d01d00000001d01601600000801d00003200801600000000000f00059d00801600001600f00800002401d00800000000000801601600801601d00000f00801600f00801600000000000f00059d00801600000000f00800002400f008000000000008000000,
  0xf00000002b00000000000000001600000f00000000000000f00000000f01600000000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000000000000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000f00000002b00000000000000000f00000f00000001d00000f00000000f00f01d00000000000001d00001d00000000000001d00003200000000000000000f00058000000000000001d00000001600f00000000000000000000001d00000000000001d00003900000000000000000f00058000000001d00000f00000002400000000000000000000000000000000000000f00000000f00000000000000000000000000000000000000f00000000f00001d00000000001d00000000000000000000f00000002b00000000000000001600000f00000001d00000f00000000f01601d00000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000001d00000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000001d00000000000001d00003900000000000000000f00058000000000000001d00000002400f00000000001d01d00000001d00000000000001d00003200000000000000000f00059d00000000000000f00000002401d00000000000000000000000000001d00000f00000000f00000000000000000f00059d00000000000000f00000002400f000000000000000000000,
  0x80160010013cf0080163eb0080160013c13c101600100f0080160010013cf00800100f3d60083c100100100801d01601d0163d60013c801d0013f20080160013c13c100f00159d0080160013c13c80080013dd3cf0083c13c100101d0010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c10010010080010160080163dd0163cf0080010240080160013c13c10080010080080160013c13d60080010243c801d0010013d60080010010080160010163cf0080163eb0080010010013c100f00100f0080163dd0013cf00801600f3cf01d3c100100100801d01601d0163d60013c801d0013f20080160013c13c100f0015880080160013c13dd0080013d63cf0083c13c13c100800100101d0163d60013c801d0013f90080160013c13c100f0015880080163dd0163cf0080010243c80083c10010010080160160080160010013cf00800100f0080160013c13c10080010080080160010013cf00801600f3c801d0013c100101d0010010080160010163cf0080163eb0080160013c13c101600100f0080163dd0013cf00801600f3d601d3c100100100801d01601d0163d60013c801d0013f20080160013c13c100f00159d0080160013c13dd0080013dd3cf0083c13c13c101d0010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c10010010080010160080163dd0163cf0080010240080160013c13c10080010080080160013c13d60080010243c801d0010013d60080010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c100100100800101601d0163d60013c801d0013f90080160013c13c100f0015880080160013c13dd0080013e43cf0083c13c13dd01d00100101d0163d60013c801d0013f20080160013c13c100f00159d0080163c10163cf0080010243dd0083c10010010080160160080163dd0013cf00801600f0080160013c13c100f00159d0080160013c13cf0080010243cf0080013c1001008001001,
  0x20020020f00000022b00000020020020001600000f00000020020020f00000020f21600020020020000001d00001d00020020020001d00023200000020020020000f00059d00000020020020000000021d20f00020020020001d00000000000020020020001d00022b00000020020020000000000f00000020020020f00000020f20000020020020000000000000000021d20020f00000022400000020020020000000000000000020020021600000022420001d20020020000000000000000020020020f00000022b00000020020020000f00000f00000021d20020f00000020f20f01d20020020000001d00001d00020020020001d00023200000020020020000f00058000000020020021d00000021620f00020020020000000000001d00020020020001d00023900000020020020000f00058000000021d20020f00000022420000020020020000000000000000020020020f00000020f00000020020020000000000000000020020020f00000020f20001d20020020001d00000000000020020020f00000022b00000020020020001600000f00000021d20020f00000020f21601d20020020000001d00001d00020020020001d00023200000020020020000f00059d00000020020021d00000021d20f00020020020001d00000000000020020020001d00022b00000020020020000000000f00000020020020f00000020f20000020020020000000000000000021d20020f00000022400000020020020000000000000000020020021600000022420001d20020020000000000000000020020020001d00022b00000020020020000000000f00000020020020f00000020f20000020020020000000000001d00020020020001d00023900000020020020000f00058000000020020021d00000022420f00020020021d01d00000001d00020020020001d00023200000020020020000f00059d00000020020020f00000022421d00020020020000000000000000021d20020f00000020f00000020020020000f00059d00000020020020f00000022420f000200200200000000000,
  0x801600000000f00801602b00801600000000001600000f00801600000000f00800000f01600800000000000801d01601d01601600000801d00003200801600000000000f00059d00801600000000800800001d00f00800000000001d00000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001600801601d01600f00800002400801600000000000800000800801600000001600800002400801d00000001600800000000801600001600f00801602b00800000000000000f00000f00801601d00000f00801600f00f01d00000000000801d01601d01601600000801d00003200801600000000000f00058800801600000001d00800001600f00800000000000800000001d01601600000801d00003900801600000000000f00058800801601d01600f00800002400800800000000000801601600801600000000f00800000f00801600000000000800000800801600000000f00801600f00801d00000000001d00000000801600001600f00801602b00801600000000001600000f00801601d00000f00801600f01601d00000000000801d01601d01601600000801d00003200801600000000000f00059d00801600000001d00800001d00f00800000000001d00000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001600801601d01600f00800002400801600000000000800000800801600000001600800002400801d00000001600800000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001601d01601600000801d00003900801600000000000f00058800801600000001d00800002400f00800000001d01d00000001d01601600000801d00003200801600000000000f00059d00801600001600f00800002401d00800000000000801601600801601d00000f00801600f00801600000000000f00059d00801600000000f00800002400f008000000000008000000,
  0xf00000002b00000000000000001600000f00000000000000f00000000f01600000000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000000000000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000f00000002b00000000000000000f00000f00000001d00000f00000000f00f01d00000000000001d00001d00000000000001d00003200000000000000000f00058000000000000001d00000001600f00000000000000000000001d00000000000001d00003900000000000000000f00058000000001d00000f00000002400000000000000000000000000000000000000f00000000f00000000000000000000000000000000000000f00000000f00001d00000000001d00000000000000000000f00000002b00000000000000001600000f00000001d00000f00000000f01601d00000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000001d00000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000001d00000000000001d00003900000000000000000f00058000000000000001d00000002400f00000000001d01d00000001d00000000000001d00003200000000000000000f00059d00000000000000f00000002401d00000000000000000000000000001d00000f00000000f00000000000000000f00059d00000000000000f00000002400f000000000000000000000,
  0x80160010013cf0080163eb0080160013c13c101600100f0080160010013cf00800100f3d60083c100100100801d01601d0163d60013c801d0013f20080160013c13c100f00159d0080160013c13c80080013dd3cf0083c13c100101d0010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c10010010080010160080163dd0163cf0080010240080160013c13c10080010080080160013c13d60080010243c801d0010013d60080010010080160010163cf0080163eb0080010010013c100f00100f0080163dd0013cf00801600f3cf01d3c100100100801d01601d0163d60013c801d0013f20080160013c13c100f0015880080160013c13dd0080013d63cf0083c13c13c100800100101d0163d60013c801d0013f90080160013c13c100f0015880080163dd0163cf0080010243c80083c10010010080160160080160010013cf00800100f0080160013c13c10080010080080160010013cf00801600f3c801d0013c100101d0010010080160010163cf0080163eb0080160013c13c101600100f0080163dd0013cf00801600f3d601d3c100100100801d01601d0163d60013c801d0013f20080160013c13c100f00159d0080160013c13dd0080013dd3cf0083c13c13c101d0010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c10010010080010160080163dd0163cf0080010240080160013c13c10080010080080160013c13d60080010243c801d0010013d60080010010080160010163c801d0163eb0080160010013c100800100f0080160010013cf00800100f3c80083c100100100800101601d0163d60013c801d0013f90080160013c13c100f0015880080160013c13dd0080013e43cf0083c13c13dd01d00100101d0163d60013c801d0013f20080160013c13c100f00159d0080163c10163cf0080010243dd0083c10010010080160160080163dd0013cf00801600f0080160013c13c100f00159d0080160013c13cf0080010243cf0080013c1001008001001,
  0xf00000002b00000000000000001600000f00000000000000f00000000f01600000000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000000000000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000f00000002b00000000000000000f00000f00000001d00000f00000000f00f01d00000000000001d00001d00000000000001d00003200000000000000000f00058000000000000001d00000001600f00000000000000000000001d00000000000001d00003900000000000000000f00058000000001d00000f00000002400000000000000000000000000000000000000f00000000f00000000000000000000000000000000000000f00000000f00001d00000000001d00000000000000000000f00000002b00000000000000001600000f00000001d00000f00000000f01601d00000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000001d00000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000001d00000000000001d00003900000000000000000f00058000000000000001d00000002400f00000000001d01d00000001d00000000000001d00003200000000000000000f00059d00000000000000f00000002401d00000000000000000000000000001d00000f00000000f00000000000000000f00059d00000000000000f00000002400f000000000000000000000,
  0x801600000000f00801602b00801600000000001600000f00801600000000f00800000f01600800000000000801d01601d01601600000801d00003200801600000000000f00059d00801600000000800800001d00f00800000000001d00000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001600801601d01600f00800002400801600000000000800000800801600000001600800002400801d00000001600800000000801600001600f00801602b00800000000000000f00000f00801601d00000f00801600f00f01d00000000000801d01601d01601600000801d00003200801600000000000f00058800801600000001d00800001600f00800000000000800000001d01601600000801d00003900801600000000000f00058800801601d01600f00800002400800800000000000801601600801600000000f00800000f00801600000000000800000800801600000000f00801600f00801d00000000001d00000000801600001600f00801602b00801600000000001600000f00801601d00000f00801600f01601d00000000000801d01601d01601600000801d00003200801600000000000f00059d00801600000001d00800001d00f00800000000001d00000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001600801601d01600f00800002400801600000000000800000800801600000001600800002400801d00000001600800000000801600001600801d01602b00801600000000000800000f00801600000000f00800000f00800800000000000800001601d01601600000801d00003900801600000000000f00058800801600000001d00800002400f00800000001d01d00000001d01601600000801d00003200801600000000000f00059d00801600001600f00800002401d00800000000000801601600801601d00000f00801600f00801600000000000f00059d00801600000000f00800002400f008000000000008000000,
  0xf00000002b00000000000000001600000f00000000000000f00000000f01600000000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000000000000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000f00000002b00000000000000000f00000f00000001d00000f00000000f00f01d00000000000001d00001d00000000000001d00003200000000000000000f00058000000000000001d00000001600f00000000000000000000001d00000000000001d00003900000000000000000f00058000000001d00000f00000002400000000000000000000000000000000000000f00000000f00000000000000000000000000000000000000f00000000f00001d00000000001d00000000000000000000f00000002b00000000000000001600000f00000001d00000f00000000f01601d00000000000001d00001d00000000000001d00003200000000000000000f00059d00000000000001d00000001d00f00000000000001d00000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000000000001d00000f00000002400000000000000000000000000000000000001600000002400001d00000000000000000000000000000000001d00002b00000000000000000000000f00000000000000f00000000f00000000000000000000000001d00000000000001d00003900000000000000000f00058000000000000001d00000002400f00000000001d01d00000001d00000000000001d00003200000000000000000f00059d00000000000000f00000002401d00000000000000000000000000001d00000f00000000f00000000000000000f00059d00000000000000f00000002400f000000000000000000000,
  0x71c00155630071c01c05475471c001502a5553801d51d50157000155630071c039554e01c1d57155470151c01d51c000e1c00155630071d55405475471c001502a7151c01c07150071c001503801c1c01c00230071c05550070151d57003800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c054770001554e0071c038054e0071c00150317151c01d57155471c001502a01c1d51d554e01c1d500002a0151c01d53800071c00150150071c070054754770000002a5553801d51d50157000155630071c039554e0071d50155470151d51d51c000e1c00155630071d55400075471c001502a7151c01c07150071c000003101c1c01c054e0071c05550070151d57151c000e1c001556301c1d538001c5471c001502a7151c01c071554770001554e0071c038054e01c1c071555c0151d51d51c000e70001554e0071c038054e0071c00150380001c01c07155471c001502a0071c039554e0071d501502a0151d51d51c00071c00155630071c070054754770001502a5553801d51d50157000155630071c039554e01c1d57155470151d51d51c000e1c00155630071d55405475471c001502a7151c01c07150071c001503801c1c01c05630071c05550070151d57153800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c054770001554e0071c038054e0071c00150317151c01d57155471c001502a01c1d51d554e01c1d500002a0151c01d53800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c000e1c001556301c1d554001c5471c001502a7151c01c07150071c001503101c1c01d554e0071c055501c0151d57151c000e1c00155630071d55405475471c001502a7151c01c071500e70001554e0071c038054e01c1c001501c0157151d51c00157000155630071c039554e5471c001502a7151c01c071554770001502a0071c038054e0071c00150380151c01d51c0,
  0x38e3a300000000038038000038e02a38e00000e00e39500000e3a300000000e38000000e70e38038e00e00e00000000000e3a300000e54038038000038e02a70e00000e00e00000038e0380000000003a300000038e38000e00e00e00000000038e39c00000e00038038000038e02a38e00000e00e38000000e38000000000e38000000000e00038e00e00e00038000000e38000000000e38000000038e03170e00000e00e38000038e02a00000e00e38000000e38e02a00e00000e00e00000038e39500000000038038000038e02a38e00000e00e39500000e3a300000000e38000000e00e38038e00e00e00000000000e3a300000e54038038000038e02a70e00000e00e00000038e03100000000038000000038e38000e00e00e00e00000000e3a300000e00038038000038e02a70e00000e00e38000000e38000000000e38000000070e38038e00e00e00038000000e38000000000e38000000038e03800e00000e00e38000038e02a00000000e38000000e38e02a38e00e00e00000000038e3a300000000038038000038e02a38e00000e00e39500000e3a300000000e38000000e70e38038e00e00e00000000000e3a300000e54038038000038e02a70e00000e00e00000038e0380000000003a300000038e38000e00e00e00e00000038e39c00000e00038038000038e02a38e00000e00e38000000e38000000000e38000000000e00038e00e00e00038000000e38000000000e38000000038e03170e00000e00e38000038e02a00000e00e38000000e38e02a00e00000e00e00000038e39c00000e00038038000038e02a38e00000e00e38000000e38000000000e38000000000e00038e00e00e00000000000e3a300000e54038038000038e02a70e00000e00e00000038e03100000000e38000000038e38000e00e00e00e00000000e3a300000e54038038000038e02a70e00000e00e38000000e38000000000e38000000000e00038e00e00e00039500000e3a300000000e38038000038e02a70e00000e00e38000038e02a00000000e38000000038e03838e00000e000,
  0x2300000000000000000000002a00038000000001570000002300000038000e01c00070000000000000000000e00000002300000054000000000000002a70000000070000000000003801c00000002300000000000000000070038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000070000000e00000038000e00000000003170000000070000000000002a01c00000000e01c00000002a00000000038000000000001500000070000000070000002a00038000000001570000002300000038000e00000000000000000000000000e00000002300000054000000000000002a70000000070000000000003101c00000000e00000000000000000070000000e00000002301c00038001c00000000002a70000000070000070000000e00000038000e01c00070001c00000000000000e70000000e00000038000e00000000003800000000070000000000002a00000038000e00000000002a00000000000000000000002300000070000000070000002a00038000000001570000002300000038000e01c00070000000000000000000e00000002300000054000000000000002a70000000070000000000003801c00000002300000000000000000070038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000070000000e00000038000e00000000003170000000070000000000002a01c00000000e01c00000002a00000000038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000e00000002301c00054001c00000000002a70000000070000000000003101c00000000e00000000001c00000070000000e00000002300000054000000000000002a70000000070000e70000000e00000038000e01c00000001c00070000000001570000002300000038000e00000000002a70000000070000070000002a00000038000e000000000038000000000000,
  0x1c00071c71e31c00070071c01c00071c71ea1c70070070071d50071c71e31c00070071c01c00077071c01c70070070071c00071c71e31c00075471c01c00071c71ea7070070070071c00071c71f81c00070071e31c00071c71c01c70070070071c00071c71dc1c00070071c01c00071c71ea1c70070070071c00071c71c01c00070071c01c00071c71c01c70070070071c00071c71c01c00070071c01c00071c71f17070070070071c00071c71ea1c00070071c01c00071c71ea1c70070070071c00071c71d51c00070071c01c00071c71ea1c70070070071d50071c71e31c00070071c01c00071c71c01c70070070071c00071c71e31c00075471c01c00071c71ea7070070070071c00071c71f11c00070071c01c00071c71c01c70070070071c00071c71e31c00070071c01c00071c71ea7070070070071c00071c71c01c00070071c01c00077071c01c70070070071c00071c71c01c00070071c01c00071c71f81c70070070071c00071c71ea1c00070071c01c00071c71ea1c70070070071c00071c71e31c00070071c01c00071c71ea1c70070070071d50071c71e31c00070071c01c00077071c01c70070070071c00071c71e31c00075471c01c00071c71ea7070070070071c00071c71f81c00070071e31c00071c71c01c70070070071c00071c71dc1c00070071c01c00071c71ea1c70070070071c00071c71c01c00070071c01c00071c71c01c70070070071c00071c71c01c00070071c01c00071c71f17070070070071c00071c71ea1c00070071c01c00071c71ea1c70070070071c00071c71dc1c00070071c01c00071c71ea1c70070070071c00071c71c01c00070071c01c00071c71c01c70070070071c00071c71e31c00075471c01c00071c71ea7070070070071c00071c71f11c00070071c01c00071c71c01c70070070071c00071c71e31c00075471c01c00071c71ea7070070070071c00071c71c01c00070071c01c00071c71c01c70070070071d50071c71e31c00070071c01c00071c71ea7070070070071c00071c71ea1c00070071c01c00071c71f81c7007007007,
  0x71c00155630071c01c05475471c001502a5553801d51d50157000155630071c039554e01c1d57155470151c01d51c000e1c00155630071d55405475471c001502a7151c01c07150071c001503801c1c01c00230071c05550070151d57003800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c054770001554e0071c038054e0071c00150317151c01d57155471c001502a01c1d51d554e01c1d500002a0151c01d53800071c00150150071c070054754770000002a5553801d51d50157000155630071c039554e0071d50155470151d51d51c000e1c00155630071d55400075471c001502a7151c01c07150071c000003101c1c01c054e0071c05550070151d57151c000e1c001556301c1d538001c5471c001502a7151c01c071554770001554e0071c038054e01c1c071555c0151d51d51c000e70001554e0071c038054e0071c00150380001c01c07155471c001502a0071c039554e0071d501502a0151d51d51c00071c00155630071c070054754770001502a5553801d51d50157000155630071c039554e01c1d57155470151d51d51c000e1c00155630071d55405475471c001502a7151c01c07150071c001503801c1c01c05630071c05550070151d57153800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c054770001554e0071c038054e0071c00150317151c01d57155471c001502a01c1d51d554e01c1d500002a0151c01d53800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c000e1c001556301c1d554001c5471c001502a7151c01c07150071c001503101c1c01d554e0071c055501c0151d57151c000e1c00155630071d55405475471c001502a7151c01c071500e70001554e0071c038054e01c1c001501c0157151d51c00157000155630071c039554e5471c001502a7151c01c071554770001502a0071c038054e0071c00150380151c01d51c0,
  0x2300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001500000000000000000000002a00000000000001500000002300000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000000000000000000002a70000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000003800000000000000000000002a00000000000000000000002a00000000000000000000002300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000000000000000000000000000000000000000000001500000002300000000000000000000002a70000000000000000000002a000000000000000000000038000000000000,
  0x2300000000000000000000002a00038000000001570000002300000038000e01c00070000000000000000000e00000002300000054000000000000002a70000000070000000000003801c00000002300000000000000000070038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000070000000e00000038000e00000000003170000000070000000000002a01c00000000e01c00000002a00000000038000000000001500000070000000070000002a00038000000001570000002300000038000e00000000000000000000000000e00000002300000054000000000000002a70000000070000000000003101c00000000e00000000000000000070000000e00000002301c00038001c00000000002a70000000070000070000000e00000038000e01c00070001c00000000000000e70000000e00000038000e00000000003800000000070000000000002a00000038000e00000000002a00000000000000000000002300000070000000070000002a00038000000001570000002300000038000e01c00070000000000000000000e00000002300000054000000000000002a70000000070000000000003801c00000002300000000000000000070038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000070000000e00000038000e00000000003170000000070000000000002a01c00000000e01c00000002a00000000038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000e00000002301c00054001c00000000002a70000000070000000000003101c00000000e00000000001c00000070000000e00000002300000054000000000000002a70000000070000e70000000e00000038000e01c00000001c00070000000001570000002300000038000e00000000002a70000000070000070000002a00000038000e000000000038000000000000,
  0x2300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001500000000000000000000002a00000000000001500000002300000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000000000000000000002a70000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000003800000000000000000000002a00000000000000000000002a00000000000000000000002300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000000000000000000000000000000000000000000001500000002300000000000000000000002a70000000000000000000002a000000000000000000000038000000000000,
  0x71c00155630071c01c05475471c001502a5553801d51d50157000155630071c039554e01c1d57155470151c01d51c000e1c00155630071d55405475471c001502a7151c01c07150071c001503801c1c01c00230071c05550070151d57003800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c054770001554e0071c038054e0071c00150317151c01d57155471c001502a01c1d51d554e01c1d500002a0151c01d53800071c00150150071c070054754770000002a5553801d51d50157000155630071c039554e0071d50155470151d51d51c000e1c00155630071d55400075471c001502a7151c01c07150071c000003101c1c01c054e0071c05550070151d57151c000e1c001556301c1d538001c5471c001502a7151c01c071554770001554e0071c038054e01c1c071555c0151d51d51c000e70001554e0071c038054e0071c00150380001c01c07155471c001502a0071c039554e0071d501502a0151d51d51c00071c00155630071c070054754770001502a5553801d51d50157000155630071c039554e01c1d57155470151d51d51c000e1c00155630071d55405475471c001502a7151c01c07150071c001503801c1c01c05630071c05550070151d57153800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c054770001554e0071c038054e0071c00150317151c01d57155471c001502a01c1d51d554e01c1d500002a0151c01d53800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c000e1c001556301c1d554001c5471c001502a7151c01c07150071c001503101c1c01d554e0071c055501c0151d57151c000e1c00155630071d55405475471c001502a7151c01c071500e70001554e0071c038054e01c1c001501c0157151d51c00157000155630071c039554e5471c001502a7151c01c071554770001502a0071c038054e0071c00150380151c01d51c0,
  0x38e3a300000000038038000038e02a38e00000e00e39500000e3a300000000e38000000e70e38038e00e00e00000000000e3a300000e54038038000038e02a70e00000e00e00000038e0380000000003a300000038e38000e00e00e00000000038e39c00000e00038038000038e02a38e00000e00e38000000e38000000000e38000000000e00038e00e00e00038000000e38000000000e38000000038e03170e00000e00e38000038e02a00000e00e38000000e38e02a00e00000e00e00000038e39500000000038038000038e02a38e00000e00e39500000e3a300000000e38000000e00e38038e00e00e00000000000e3a300000e54038038000038e02a70e00000e00e00000038e03100000000038000000038e38000e00e00e00e00000000e3a300000e00038038000038e02a70e00000e00e38000000e38000000000e38000000070e38038e00e00e00038000000e38000000000e38000000038e03800e00000e00e38000038e02a00000000e38000000e38e02a38e00e00e00000000038e3a300000000038038000038e02a38e00000e00e39500000e3a300000000e38000000e70e38038e00e00e00000000000e3a300000e54038038000038e02a70e00000e00e00000038e0380000000003a300000038e38000e00e00e00e00000038e39c00000e00038038000038e02a38e00000e00e38000000e38000000000e38000000000e00038e00e00e00038000000e38000000000e38000000038e03170e00000e00e38000038e02a00000e00e38000000e38e02a00e00000e00e00000038e39c00000e00038038000038e02a38e00000e00e38000000e38000000000e38000000000e00038e00e00e00000000000e3a300000e54038038000038e02a70e00000e00e00000038e03100000000e38000000038e38000e00e00e00e00000000e3a300000e54038038000038e02a70e00000e00e38000000e38000000000e38000000000e00038e00e00e00039500000e3a300000000e38038000038e02a70e00000e00e38000038e02a00000000e38000000038e03838e00000e000,
  0x2300000000000000000000002a00038000000001570000002300000038000e01c00070000000000000000000e00000002300000054000000000000002a70000000070000000000003801c00000002300000000000000000070038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000070000000e00000038000e00000000003170000000070000000000002a01c00000000e01c00000002a00000000038000000000001500000070000000070000002a00038000000001570000002300000038000e00000000000000000000000000e00000002300000054000000000000002a70000000070000000000003101c00000000e00000000000000000070000000e00000002301c00038001c00000000002a70000000070000070000000e00000038000e01c00070001c00000000000000e70000000e00000038000e00000000003800000000070000000000002a00000038000e00000000002a00000000000000000000002300000070000000070000002a00038000000001570000002300000038000e01c00070000000000000000000e00000002300000054000000000000002a70000000070000000000003801c00000002300000000000000000070038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000070000000e00000038000e00000000003170000000070000000000002a01c00000000e01c00000002a00000000038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000e00000002301c00054001c00000000002a70000000070000000000003101c00000000e00000000001c00000070000000e00000002300000054000000000000002a70000000070000e70000000e00000038000e01c00000001c00070000000001570000002300000038000e00000000002a70000000070000070000002a00000038000e000000000038000000000000,
  0x2300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001500000000000000000000002a00000000000001500000002300000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000000000000000000002a70000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000003800000000000000000000002a00000000000000000000002a00000000000000000000002300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000000000000000000000000000000000000000000001500000002300000000000000000000002a70000000000000000000002a000000000000000000000038000000000000,
  0x71c00155630071c01c05475471c001502a5553801d51d50157000155630071c039554e01c1d57155470151c01d51c000e1c00155630071d55405475471c001502a7151c01c07150071c001503801c1c01c00230071c05550070151d57003800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c054770001554e0071c038054e0071c00150317151c01d57155471c001502a01c1d51d554e01c1d500002a0151c01d53800071c00150150071c070054754770000002a5553801d51d50157000155630071c039554e0071d50155470151d51d51c000e1c00155630071d55400075471c001502a7151c01c07150071c000003101c1c01c054e0071c05550070151d57151c000e1c001556301c1d538001c5471c001502a7151c01c071554770001554e0071c038054e01c1c071555c0151d51d51c000e70001554e0071c038054e0071c00150380001c01c07155471c001502a0071c039554e0071d501502a0151d51d51c00071c00155630071c070054754770001502a5553801d51d50157000155630071c039554e01c1d57155470151d51d51c000e1c00155630071d55405475471c001502a7151c01c07150071c001503801c1c01c05630071c05550070151d57153800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c054770001554e0071c038054e0071c00150317151c01d57155471c001502a01c1d51d554e01c1d500002a0151c01d53800071c001501c0071d51c05475471c001502a0153801d51d500e70001554e0071c038054e01c1c00000070157001d51c000e1c001556301c1d554001c5471c001502a7151c01c07150071c001503101c1c01d554e0071c055501c0151d57151c000e1c00155630071d55405475471c001502a7151c01c071500e70001554e0071c038054e01c1c001501c0157151d51c00157000155630071c039554e5471c001502a7151c01c071554770001502a0071c038054e0071c00150380151c01d51c0,
  0x2300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001500000000000000000000002a00000000000001500000002300000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000000000000000000002a70000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000003800000000000000000000002a00000000000000000000002a00000000000000000000002300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000000000000000000000000000000000000000000001500000002300000000000000000000002a70000000000000000000002a000000000000000000000038000000000000,
  0x2300000000000000000000002a00038000000001570000002300000038000e01c00070000000000000000000e00000002300000054000000000000002a70000000070000000000003801c00000002300000000000000000070038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000070000000e00000038000e00000000003170000000070000000000002a01c00000000e01c00000002a00000000038000000000001500000070000000070000002a00038000000001570000002300000038000e00000000000000000000000000e00000002300000054000000000000002a70000000070000000000003101c00000000e00000000000000000070000000e00000002301c00038001c00000000002a70000000070000070000000e00000038000e01c00070001c00000000000000e70000000e00000038000e00000000003800000000070000000000002a00000038000e00000000002a00000000000000000000002300000070000000070000002a00038000000001570000002300000038000e01c00070000000000000000000e00000002300000054000000000000002a70000000070000000000003801c00000002300000000000000000070038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000070000000e00000038000e00000000003170000000070000000000002a01c00000000e01c00000002a00000000038000000000001c00000000000000000000002a00038000000000e70000000e00000038000e01c00000000000070000000000e00000002301c00054001c00000000002a70000000070000000000003101c00000000e00000000001c00000070000000e00000002300000054000000000000002a70000000070000e70000000e00000038000e01c00000001c00070000000001570000002300000038000e00000000002a70000000070000070000002a00000038000e000000000038000000000000,
  0x2300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001500000000000000000000002a00000000000001500000002300000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000000000000000000002a70000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000003800000000000000000000002a00000000000000000000002a00000000000000000000002300000000000000000000002a00000000000001500000002300000000000000000070000000000000000000000000002300000054000000000000002a70000000000000000000003800000000002300000000000000000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003170000000000000000000002a00000000000000000000002a00000000000000000000001c00000000000000000000002a00000000000000000000000000000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000003100000000000000000000000000000000000000000000002300000054000000000000002a70000000000000000000000000000000000000000000000000000000000001500000002300000000000000000000002a70000000000000000000002a000000000000000000000038000000000000,
  0x50019b5006cd5001a26c00140141a95000065001a218000000035b50050d5001a218001451418d50000d5006cd1805005001865006cd01419b6c00140001a950000650018618050000036900001b51418d6c00145001a25000145001943400000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd34000050034650000d5001a21800140005295000065001a219b5000141a950000651418d18000001419b5000065001a218000000019b50000d5001a26c00140141b00000065001a218000000034650050d5001a218001451418d50000d5006cd1800005001865006cd01419b6c00140001a95000065001861805000005290000060141a21800145001a250000d50018d34000050018650000d0141941800140141a950000650018618050050034650000d5001a21800145141a25000225006cd50001b00034650050d5001a218001400036900001b5006c61805000006f75000065001a218001400019450000600018d18000050019b5006cd5001a26c00140141b05000065001a218000000035b50050d5001a218001451418d50000d5006cd1805005001865006cd01419b6c00140001a950000650018618050000052900001b5141a26c00145001a25000145001943400000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd34000050034650000d5001a21800140005295000065001a219b5000141a950000651418d18000001419b5000065001a21800000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd3400005001865006cd01419b6c00140141a95000065001861805000005295000065141a21800145001a25000145001943400005001865006cd01419b6c00140001a950000650018618050050034650050d5001a21800145141a250000d0006cd50000000035b50050d5001a21800140141a95000065001861805000141b05000065001a21800145001a250001b5001a2180000,
  0x3400003406c034002200d00d00d02934034034002200000034000034034034002200000d34d00034000034000000034d3400003406c034d01b00d00d00d02934034034000000034000d02934034034d00000000d34002234001434001400000d00000034002234001400d00d00d03734034034000001b00034000034034034002200000d34d00034000034000000034034000034034034002200000d00d52934034034002201b34000d02934034034d00000000d34d01b34034034002200000000000034000034002200d00d00d03034034034002200000034000034034034002200000d34d00034000034000000034d3400003406c034d01b00d00d00d02934034034000000034000d52934034034d02200000d34002234000034000000000d34000034000034d01400d00d00d02934034034000000034034000034034034002200000d34d02234002234000050035b34000034034034002200000d00d02934034034000000034000d03734034034002200000d3400143403403400000000003400003406c034002200d00d00d03034034034002200000034000034034034002200000d34d00034000034000000034d3400003406c034d01b00d00d00d02934034034000000034000d52934034034d02200000d34002234001434001400000d00000034002234001400d00d00d03734034034000001b00034000034034034002200000d34d00034000034000000034034000034034034002200000d00d52934034034002201b34000d02934034034d00000000d34d01b34034034002200000000000034002234001400d00d00d03734034034000001b00034000034034034002200000d34d0003400003400000003403400003406c034d01b00d00d00d02934034034000000034000d52934034034d02200000d34002234001434001400000d3400003406c034d01b00d00d00d02934034034000000034034000034034034002200000d34d02234000034000050034034000034034034002200000d00d02934034034000000034000d03034034034002200000d340022340340340022000000,
  0x1b0006cd0000226c000000002900000000002200000000035b00000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000036900001b00000d6c00000000220000140000143400000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd34000000034000000d00002200000000052900000000002201b00000002900000000000d00000000001b00000000002200000000001b00000d0000226c000000003000000000002200000000034000000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000052900000000002200000000002200000d00000d34000000000000000d00001400000000002900000000000000000000034000000d0000220000000000220000220006cd50001b00034000000d00002200000000036900001b0006c00000000006f700000000002200000000001400000000000d00000000001b0006cd0000226c000000003000000000002200000000035b00000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000052900001b0000226c00000000220000140000143400000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd34000000034000000d00002200000000052900000000002201b00000002900000000000d00000000001b0000000000220000000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd3400000000000006cd00001b6c00000000290000000000000000000005290000000000220000000000220000140000143400000000000006cd00001b6c000000002900000000000000000000034000000d00002200000000002200000d0006cd50000000035b00000d00002200000000002900000000000000000000003000000000002200000000002200001b000022000000,
  0x1860001866c01860220061861860291861801860220061861860001861801860220061861860001861801860000061861860001866c018601b0061861860291861801860000061861860291861801860000061861860221861941860140061861860001861a218601400618618603718618018600001b18618600018618018602200618618600018618018600000618618600018618018602200618618652918618018602201b18618602918618018600000618618601b1861801860220061861860001861801860220061861860301861801860220061861860001861801860220061861860001861801860000061861860001866c018601b0061861860291861801860000061861865291861801860220061861860221861801860000061861860001861801860140061861860291861801860000061861860001861801860220061861860221861a218600050619b1860001861801860220061861860291861801860000061861860371861801860220061861860141861801860000061861860001866c01860220061861860301861801860220061861860001861801860220061861860001861801860000061861860001866c018601b0061861860291861801860000061861865291861801860220061861860221861941860140061861860001861a218601400618618603718618018600001b18618600018618018602200618618600018618018600000618618600018618018602200618618652918618018602201b18618602918618018600000618618601b1861801860220061861860001861a218601400618618603718618018600001b1861860001861801860220061861860001861801860000061861860001866c018601b0061861860291861801860000061861865291861801860220061861860221861941860140061861860001866c018601b006186186029186180186000006186186000186180186022006186186022186180186000506186186000186180186022006186186029186180186000006186186030186180186022006186186022186180186022006186,
  0x50019b5006cd5001a26c00140141a95000065001a218000000035b50050d5001a218001451418d50000d5006cd1805005001865006cd01419b6c00140001a950000650018618050000036900001b51418d6c00145001a25000145001943400000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd34000050034650000d5001a21800140005295000065001a219b5000141a950000651418d18000001419b5000065001a218000000019b50000d5001a26c00140141b00000065001a218000000034650050d5001a218001451418d50000d5006cd1800005001865006cd01419b6c00140001a95000065001861805000005290000060141a21800145001a250000d50018d34000050018650000d0141941800140141a950000650018618050050034650000d5001a21800145141a25000225006cd50001b00034650050d5001a218001400036900001b5006c61805000006f75000065001a218001400019450000600018d18000050019b5006cd5001a26c00140141b05000065001a218000000035b50050d5001a218001451418d50000d5006cd1805005001865006cd01419b6c00140001a950000650018618050000052900001b5141a26c00145001a25000145001943400000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd34000050034650000d5001a21800140005295000065001a219b5000141a950000651418d18000001419b5000065001a21800000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd3400005001865006cd01419b6c00140141a95000065001861805000005295000065141a21800145001a25000145001943400005001865006cd01419b6c00140001a950000650018618050050034650050d5001a21800145141a250000d0006cd50000000035b50050d5001a21800140141a95000065001861805000141b05000065001a21800145001a250001b5001a2180000,
  0x6c00000220000000000290000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000002900000000000000000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b0000000000220000000000000000000000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200000000000000000000000000000000001400000000002900000000000000000000000000000000002200000000002200002200000050001b0000000000000000220000000000290000000000000000000000370000000000220000000000140000000000000000000000000006c00000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b00000000002200000000000000002200001400000000003700000000000001b0000000000000000000220000000000000000000000000000000000000006c000001b0000000000290000000000000000000005290000000000220000000000220000140000140000000000000006c000001b000000000029000000000000000000000000000000000022000000000022000000000000500000000000000000000022000000000029000000000000000000000030000000000022000000000022000000000022000000,
  0x1b0006cd0000226c000000002900000000002200000000035b00000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000036900001b00000d6c00000000220000140000143400000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd34000000034000000d00002200000000052900000000002201b00000002900000000000d00000000001b00000000002200000000001b00000d0000226c000000003000000000002200000000034000000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000052900000000002200000000002200000d00000d34000000000000000d00001400000000002900000000000000000000034000000d0000220000000000220000220006cd50001b00034000000d00002200000000036900001b0006c00000000006f700000000002200000000001400000000000d00000000001b0006cd0000226c000000003000000000002200000000035b00000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000052900001b0000226c00000000220000140000143400000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd34000000034000000d00002200000000052900000000002201b00000002900000000000d00000000001b0000000000220000000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd3400000000000006cd00001b6c00000000290000000000000000000005290000000000220000000000220000140000143400000000000006cd00001b6c000000002900000000000000000000034000000d00002200000000002200000d0006cd50000000035b00000d00002200000000002900000000000000000000003000000000002200000000002200001b000022000000,
  0x6c00000220000000000290000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000002900000000000000000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b0000000000220000000000000000000000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200000000000000000000000000000000001400000000002900000000000000000000000000000000002200000000002200002200000050001b0000000000000000220000000000290000000000000000000000370000000000220000000000140000000000000000000000000006c00000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b00000000002200000000000000002200001400000000003700000000000001b0000000000000000000220000000000000000000000000000000000000006c000001b0000000000290000000000000000000005290000000000220000000000220000140000140000000000000006c000001b000000000029000000000000000000000000000000000022000000000022000000000000500000000000000000000022000000000029000000000000000000000030000000000022000000000022000000000022000000,
  0x50019b5006cd5001a26c00140141a95000065001a218000000035b50050d5001a218001451418d50000d5006cd1805005001865006cd01419b6c00140001a950000650018618050000036900001b51418d6c00145001a25000145001943400000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd34000050034650000d5001a21800140005295000065001a219b5000141a950000651418d18000001419b5000065001a218000000019b50000d5001a26c00140141b00000065001a218000000034650050d5001a218001451418d50000d5006cd1800005001865006cd01419b6c00140001a95000065001861805000005290000060141a21800145001a250000d50018d34000050018650000d0141941800140141a950000650018618050050034650000d5001a21800145141a25000225006cd50001b00034650050d5001a218001400036900001b5006c61805000006f75000065001a218001400019450000600018d18000050019b5006cd5001a26c00140141b05000065001a218000000035b50050d5001a218001451418d50000d5006cd1805005001865006cd01419b6c00140001a950000650018618050000052900001b5141a26c00145001a25000145001943400000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd34000050034650000d5001a21800140005295000065001a219b5000141a950000651418d18000001419b5000065001a21800000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd3400005001865006cd01419b6c00140141a95000065001861805000005295000065141a21800145001a25000145001943400005001865006cd01419b6c00140001a950000650018618050050034650050d5001a21800145141a250000d0006cd50000000035b50050d5001a21800140141a95000065001861805000141b05000065001a21800145001a250001b5001a2180000,
  0x3400003406c034002200d00d00d02934034034002200000034000034034034002200000d34d00034000034000000034d3400003406c034d01b00d00d00d02934034034000000034000d02934034034d00000000d34002234001434001400000d00000034002234001400d00d00d03734034034000001b00034000034034034002200000d34d00034000034000000034034000034034034002200000d00d52934034034002201b34000d02934034034d00000000d34d01b34034034002200000000000034000034002200d00d00d03034034034002200000034000034034034002200000d34d00034000034000000034d3400003406c034d01b00d00d00d02934034034000000034000d52934034034d02200000d34002234000034000000000d34000034000034d01400d00d00d02934034034000000034034000034034034002200000d34d02234002234000050035b34000034034034002200000d00d02934034034000000034000d03734034034002200000d3400143403403400000000003400003406c034002200d00d00d03034034034002200000034000034034034002200000d34d00034000034000000034d3400003406c034d01b00d00d00d02934034034000000034000d52934034034d02200000d34002234001434001400000d00000034002234001400d00d00d03734034034000001b00034000034034034002200000d34d00034000034000000034034000034034034002200000d00d52934034034002201b34000d02934034034d00000000d34d01b34034034002200000000000034002234001400d00d00d03734034034000001b00034000034034034002200000d34d0003400003400000003403400003406c034d01b00d00d00d02934034034000000034000d52934034034d02200000d34002234001434001400000d3400003406c034d01b00d00d00d02934034034000000034034000034034034002200000d34d02234000034000050034034000034034034002200000d00d02934034034000000034000d03034034034002200000d340022340340340022000000,
  0x1b0006cd0000226c000000002900000000002200000000035b00000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000036900001b00000d6c00000000220000140000143400000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd34000000034000000d00002200000000052900000000002201b00000002900000000000d00000000001b00000000002200000000001b00000d0000226c000000003000000000002200000000034000000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000052900000000002200000000002200000d00000d34000000000000000d00001400000000002900000000000000000000034000000d0000220000000000220000220006cd50001b00034000000d00002200000000036900001b0006c00000000006f700000000002200000000001400000000000d00000000001b0006cd0000226c000000003000000000002200000000035b00000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000052900001b0000226c00000000220000140000143400000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd34000000034000000d00002200000000052900000000002201b00000002900000000000d00000000001b0000000000220000000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd3400000000000006cd00001b6c00000000290000000000000000000005290000000000220000000000220000140000143400000000000006cd00001b6c000000002900000000000000000000034000000d00002200000000002200000d0006cd50000000035b00000d00002200000000002900000000000000000000003000000000002200000000002200001b000022000000,
  0x6c00000220000000000290000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000002900000000000000000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b0000000000220000000000000000000000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200000000000000000000000000000000001400000000002900000000000000000000000000000000002200000000002200002200000050001b0000000000000000220000000000290000000000000000000000370000000000220000000000140000000000000000000000000006c00000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b00000000002200000000000000002200001400000000003700000000000001b0000000000000000000220000000000000000000000000000000000000006c000001b0000000000290000000000000000000005290000000000220000000000220000140000140000000000000006c000001b000000000029000000000000000000000000000000000022000000000022000000000000500000000000000000000022000000000029000000000000000000000030000000000022000000000022000000000022000000,
  0x50019b5006cd5001a26c00140141a95000065001a218000000035b50050d5001a218001451418d50000d5006cd1805005001865006cd01419b6c00140001a950000650018618050000036900001b51418d6c00145001a25000145001943400000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd34000050034650000d5001a21800140005295000065001a219b5000141a950000651418d18000001419b5000065001a218000000019b50000d5001a26c00140141b00000065001a218000000034650050d5001a218001451418d50000d5006cd1800005001865006cd01419b6c00140001a95000065001861805000005290000060141a21800145001a250000d50018d34000050018650000d0141941800140141a950000650018618050050034650000d5001a21800145141a25000225006cd50001b00034650050d5001a218001400036900001b5006c61805000006f75000065001a218001400019450000600018d18000050019b5006cd5001a26c00140141b05000065001a218000000035b50050d5001a218001451418d50000d5006cd1805005001865006cd01419b6c00140001a950000650018618050000052900001b5141a26c00145001a25000145001943400000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd34000050034650000d5001a21800140005295000065001a219b5000141a950000651418d18000001419b5000065001a21800000001860000220001946c00140006f750000650018619b00000034650050d5001a218001451418d50000d0006cd3400005001865006cd01419b6c00140141a95000065001861805000005295000065141a21800145001a25000145001943400005001865006cd01419b6c00140001a950000650018618050050034650050d5001a21800145141a250000d0006cd50000000035b50050d5001a21800140141a95000065001861805000141b05000065001a21800145001a250001b5001a2180000,
  0x6c00000220000000000290000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000002900000000000000000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b0000000000220000000000000000000000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200000000000000000000000000000000001400000000002900000000000000000000000000000000002200000000002200002200000050001b0000000000000000220000000000290000000000000000000000370000000000220000000000140000000000000000000000000006c00000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b00000000002200000000000000002200001400000000003700000000000001b0000000000000000000220000000000000000000000000000000000000006c000001b0000000000290000000000000000000005290000000000220000000000220000140000140000000000000006c000001b000000000029000000000000000000000000000000000022000000000022000000000000500000000000000000000022000000000029000000000000000000000030000000000022000000000022000000000022000000,
  0x1b0006cd0000226c000000002900000000002200000000035b00000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000036900001b00000d6c00000000220000140000143400000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd34000000034000000d00002200000000052900000000002201b00000002900000000000d00000000001b00000000002200000000001b00000d0000226c000000003000000000002200000000034000000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000052900000000002200000000002200000d00000d34000000000000000d00001400000000002900000000000000000000034000000d0000220000000000220000220006cd50001b00034000000d00002200000000036900001b0006c00000000006f700000000002200000000001400000000000d00000000001b0006cd0000226c000000003000000000002200000000035b00000d00002200000000000d00000d0006cd0000000000000006cd00001b6c000000002900000000000000000000052900001b0000226c00000000220000140000143400000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd34000000034000000d00002200000000052900000000002201b00000002900000000000d00000000001b0000000000220000000000000000220000146c00000006f700000000000001b00000034000000d00002200000000000d00000d0006cd3400000000000006cd00001b6c00000000290000000000000000000005290000000000220000000000220000140000143400000000000006cd00001b6c000000002900000000000000000000034000000d00002200000000002200000d0006cd50000000035b00000d00002200000000002900000000000000000000003000000000002200000000002200001b000022000000,
  0x6c00000220000000000290000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000002900000000000000000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b0000000000220000000000000000000000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200000000000000000000000000000000001400000000002900000000000000000000000000000000002200000000002200002200000050001b0000000000000000220000000000290000000000000000000000370000000000220000000000140000000000000000000000000006c00000220000000000300000000000220000000000000000000000220000000000000000000000000000000000000006c000001b00000000002900000000000000000000052900000000002200000000002200001400001400000000000000002200001400000000003700000000000001b00000000000000000002200000000000000000000000000000000000000000000002200000000052900000000002201b00000002900000000000000000000001b00000000002200000000000000002200001400000000003700000000000001b0000000000000000000220000000000000000000000000000000000000006c000001b0000000000290000000000000000000005290000000000220000000000220000140000140000000000000006c000001b000000000029000000000000000000000000000000000022000000000022000000000000500000000000000000000022000000000029000000000000000000000030000000000022000000000022000000000022000000,
  0x14084568001384030515301330015a1404d3a001533006808404c51404d38403051400134c0305a0001314014c14001314030514001330030515301330015a1404d3a006853130008401451404c04d3305853000840305a000131408454c001314031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c1400001403051404d385a30514001368015a6804d3d8015a3004c030015a1404d34c03056800003008456804c01403053000008403051404d385a3051530003001456804c0a001533000008403051404d38403051400133003054c001314014c14001314030514001330030515301330015a1404d3a0068530000030015a6804d369330515300085a305a0001314030530001314030514001330084515301330015a1404d3a006853000001403051404d385a3051400134d3305a004d314014c1400008404c51404d38403051400138401451404c0bc08453134c030069a6804c08403051400133003051404d36803053000008408456804d385a30515301330015a6804d3a001533006808404c51404d38403051400134c0305a0001314014c14001314030514001330030515301330015a1404d3a0068531300084015a6804d369330585300085a305a000131408454c001314031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c1400001403051404d385a30514001368015a6804d3d8015a3004c030015a1404d34c03056800003008456804c014030530000014031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c14000014030514001330084515301330015a1404d3a0068530000068015a6804d369330515300085a305a0001314030530001314030514001330030515301330015a1404d3a006853130008404c51404d385a305140013693305d804d368014c1400008404c51404d384030514001330015a1404d3a0068531300030015a6804d385a30514001385a3056804d3680305840013,
  0x84000030c84000000c00c00c00000030ca0001300c6808404c000030c84000000000c4cc000a0000c00000000030c00000000030c00000000c00c00c00000030ca0000000c30084c00000030c4cc00084c00c840000a0000c0008404c000c00000000030c00000000c00c00c00000030ca0000000c0008404c000030c84000000000c4cc000bc030c00000000030c00000000030c85a00000000c68c00000030cd8000000c30000c00000030c4cc00000000c00084000030c00000000000084000000030c85a00000c00c00c00000030ca0001300c00084000000030c84000000000c00c0004c000c00000000030c00000000030c00000000c00c00c00000030ca0000000c30000c00000030c68c00000c00c85a000a0000c00000000000c00000000030c00084000c00c00c00000030ca0000000c30000000000030c85a00000000c4cc000a0030c00000000030c8404c000030c84000000000c84c00000030cbc084000c30000c00000030c84000000000c00000000030c00000000000084084000030c85a00000c00c00c00000030ca0001300c6808404c000030c84000000000c4cc000a0000c00000000030c00000000030c00000000c00c00c00000030ca0000000c30084c00000030c68c00084c00c85a000a0000c0008404c000c00000000030c00000000c00c00c00000030ca0000000c0008404c000030c84000000000c4cc000bc030c00000000030c00000000030c85a00000000c68c00000030cd8000000c30000c00000030c4cc00000000c00084000030c00000000000000000000030c00000000c00c00c00000030ca0000000c0008404c000030c84000000000c4cc000bc030c00000000030c00000000030c00084000c00c00c00000030ca0000000c30068c00000030c68c00000c00c85a000a0000c00000000000c00000000030c00000000c00c00c00000030ca0000000c3008404c000030c85a00000000c68c000d8030c00000000030c8404c000030c84000000000c00c00000030ca0000000c30000c00000030c85a00000000c85a00000030c00000084000c,
  0x84068000084030000000030001a000000a000133006808404c00000008403000000004c0300a0000000000c00000000030000000030030000000030001a000000a006803000008400000000004c0300840000840300a000000008404c000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000085a30000000068001a680000d8001a30000030001a0000004c030068000030084068000000030030000084030000000085a300000000300000680000a000133000008403000000008403000000003003004c000000000c00000000030000000030030000000030001a000000a0068030000030001a68000068030000000085a300a0000000030030000000030000000030084000000030001a000000a0068030000000030000000085a3000000004c0300a0000000000c0000008404c0000000840300000000840000000000bc084030000030069a68000084030000000030030000000068030030000084084068000085a30000000030001a680000a000133006808404c00000008403000000004c0300a0000000000c00000000030000000030030000000030001a000000a0068030000084001a68000068030084000085a300a000000008404c000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000085a30000000068001a680000d8001a30000030001a0000004c030068000030084068000000030030000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000030084000000030001a000000a0068030000068001a68000068030000000085a300a0000000030030000000030000000030030000000030001a000000a006803000008404c000000085a300000000680300d8000068000c0000008404c000000084030000000030001a000000a0068030000030001a68000085a30000000085a300680000680300840000,
  0x5840005145845000005145005000005145a050130056858454c00051458450000051454c5000a05145005000005145005000005145005000005145005000005145a050000051458450000051454c5000845145845000a051450058404c5145005000005145005000005145005000005145a050000051458454c00051458450000051454c5000bc514500500000514500500000514585a000005145685000005145d850000051450050000051454c500000514500584000514500500000514584500000514585a000005145005000005145a050130051458450000051458450000051450050004c5145005000005145005000005145005000005145005000005145a0500000514500500000514568500000514585a000a05145005000005145005000005145005840005145005000005145a0500000514500500000514585a0000051454c5000a051450050000051458454c0005145845000005145845000005145bc584000514500500000514584500000514500500000514500500000514584584000514585a000005145005000005145a050130056858454c00051458450000051454c5000a05145005000005145005000005145005000005145005000005145a0500000514584500000514568500084514585a000a051450058404c5145005000005145005000005145005000005145a050000051458454c00051458450000051454c5000bc514500500000514500500000514585a000005145685000005145d850000051450050000051454c5000005145005840005145005000005145005000005145005000005145005000005145a050000051458454c00051458450000051454c5000bc5145005000005145005000005145005840005145005000005145a0500000514568500000514568500000514585a000a05145005000005145005000005145005000005145005000005145a050000051458454c000514585a000005145685000d851450050000051458454c0005145845000005145005000005145a0500000514500500000514585a00000514585a000005145005000845145,
  0x14084568001384030515301330015a1404d3a001533006808404c51404d38403051400134c0305a0001314014c14001314030514001330030515301330015a1404d3a006853130008401451404c04d3305853000840305a000131408454c001314031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c1400001403051404d385a30514001368015a6804d3d8015a3004c030015a1404d34c03056800003008456804c01403053000008403051404d385a3051530003001456804c0a001533000008403051404d38403051400133003054c001314014c14001314030514001330030515301330015a1404d3a0068530000030015a6804d369330515300085a305a0001314030530001314030514001330084515301330015a1404d3a006853000001403051404d385a3051400134d3305a004d314014c1400008404c51404d38403051400138401451404c0bc08453134c030069a6804c08403051400133003051404d36803053000008408456804d385a30515301330015a6804d3a001533006808404c51404d38403051400134c0305a0001314014c14001314030514001330030515301330015a1404d3a0068531300084015a6804d369330585300085a305a000131408454c001314031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c1400001403051404d385a30514001368015a6804d3d8015a3004c030015a1404d34c03056800003008456804c014030530000014031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c14000014030514001330084515301330015a1404d3a0068530000068015a6804d369330515300085a305a0001314030530001314030514001330030515301330015a1404d3a006853130008404c51404d385a305140013693305d804d368014c1400008404c51404d384030514001330015a1404d3a0068531300030015a6804d385a30514001385a3056804d3680305840013,
  0x840000000840000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a000000000008400000000004c0000840000840000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c000000000000084000000000000000000084000000000085a000000000000000000000a000130000008400000000008400000000000000004c0000000000000000000000000000000000000000000000000000a0000000000000000000000068000000000085a000a00000000000000000000000000000000840000000000000000000a0000000000000000000000085a0000000004c0000a000000000000000008404c0000000840000000000840000000000bc084000000000000000000084000000000000000000000000000000000084084000000085a000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a0000000000084000000000068000084000085a000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c0000000000000840000000000000000000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc0000000000000000000000000000000840000000000000000000a0000000000068000000000068000000000085a000a00000000000000000000000000000000000000000000000000000a000000000008404c000000085a000000000680000d800000000000000008404c0000000840000000000000000000000a0000000000000000000000085a00000000085a000000000000000840000,
  0x84068000084030000000030001a000000a000133006808404c00000008403000000004c0300a0000000000c00000000030000000030030000000030001a000000a006803000008400000000004c0300840000840300a000000008404c000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000085a30000000068001a680000d8001a30000030001a0000004c030068000030084068000000030030000084030000000085a300000000300000680000a000133000008403000000008403000000003003004c000000000c00000000030000000030030000000030001a000000a0068030000030001a68000068030000000085a300a0000000030030000000030000000030084000000030001a000000a0068030000000030000000085a3000000004c0300a0000000000c0000008404c0000000840300000000840000000000bc084030000030069a68000084030000000030030000000068030030000084084068000085a30000000030001a680000a000133006808404c00000008403000000004c0300a0000000000c00000000030000000030030000000030001a000000a0068030000084001a68000068030084000085a300a000000008404c000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000085a30000000068001a680000d8001a30000030001a0000004c030068000030084068000000030030000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000030084000000030001a000000a0068030000068001a68000068030000000085a300a0000000030030000000030000000030030000000030001a000000a006803000008404c000000085a300000000680300d8000068000c0000008404c000000084030000000030001a000000a0068030000030001a68000085a30000000085a300680000680300840000,
  0x840000000840000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a000000000008400000000004c0000840000840000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c000000000000084000000000000000000084000000000085a000000000000000000000a000130000008400000000008400000000000000004c0000000000000000000000000000000000000000000000000000a0000000000000000000000068000000000085a000a00000000000000000000000000000000840000000000000000000a0000000000000000000000085a0000000004c0000a000000000000000008404c0000000840000000000840000000000bc084000000000000000000084000000000000000000000000000000000084084000000085a000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a0000000000084000000000068000084000085a000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c0000000000000840000000000000000000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc0000000000000000000000000000000840000000000000000000a0000000000068000000000068000000000085a000a00000000000000000000000000000000000000000000000000000a000000000008404c000000085a000000000680000d800000000000000008404c0000000840000000000000000000000a0000000000000000000000085a00000000085a000000000000000840000,
  0x14084568001384030515301330015a1404d3a001533006808404c51404d38403051400134c0305a0001314014c14001314030514001330030515301330015a1404d3a006853130008401451404c04d3305853000840305a000131408454c001314031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c1400001403051404d385a30514001368015a6804d3d8015a3004c030015a1404d34c03056800003008456804c01403053000008403051404d385a3051530003001456804c0a001533000008403051404d38403051400133003054c001314014c14001314030514001330030515301330015a1404d3a0068530000030015a6804d369330515300085a305a0001314030530001314030514001330084515301330015a1404d3a006853000001403051404d385a3051400134d3305a004d314014c1400008404c51404d38403051400138401451404c0bc08453134c030069a6804c08403051400133003051404d36803053000008408456804d385a30515301330015a6804d3a001533006808404c51404d38403051400134c0305a0001314014c14001314030514001330030515301330015a1404d3a0068531300084015a6804d369330585300085a305a000131408454c001314031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c1400001403051404d385a30514001368015a6804d3d8015a3004c030015a1404d34c03056800003008456804c014030530000014031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c14000014030514001330084515301330015a1404d3a0068530000068015a6804d369330515300085a305a0001314030530001314030514001330030515301330015a1404d3a006853130008404c51404d385a305140013693305d804d368014c1400008404c51404d384030514001330015a1404d3a0068531300030015a6804d385a30514001385a3056804d3680305840013,
  0x84000030c84000000c00c00c00000030ca0001300c6808404c000030c84000000000c4cc000a0000c00000000030c00000000030c00000000c00c00c00000030ca0000000c30084c00000030c4cc00084c00c840000a0000c0008404c000c00000000030c00000000c00c00c00000030ca0000000c0008404c000030c84000000000c4cc000bc030c00000000030c00000000030c85a00000000c68c00000030cd8000000c30000c00000030c4cc00000000c00084000030c00000000000084000000030c85a00000c00c00c00000030ca0001300c00084000000030c84000000000c00c0004c000c00000000030c00000000030c00000000c00c00c00000030ca0000000c30000c00000030c68c00000c00c85a000a0000c00000000000c00000000030c00084000c00c00c00000030ca0000000c30000000000030c85a00000000c4cc000a0030c00000000030c8404c000030c84000000000c84c00000030cbc084000c30000c00000030c84000000000c00000000030c00000000000084084000030c85a00000c00c00c00000030ca0001300c6808404c000030c84000000000c4cc000a0000c00000000030c00000000030c00000000c00c00c00000030ca0000000c30084c00000030c68c00084c00c85a000a0000c0008404c000c00000000030c00000000c00c00c00000030ca0000000c0008404c000030c84000000000c4cc000bc030c00000000030c00000000030c85a00000000c68c00000030cd8000000c30000c00000030c4cc00000000c00084000030c00000000000000000000030c00000000c00c00c00000030ca0000000c0008404c000030c84000000000c4cc000bc030c00000000030c00000000030c00084000c00c00c00000030ca0000000c30068c00000030c68c00000c00c85a000a0000c00000000000c00000000030c00000000c00c00c00000030ca0000000c3008404c000030c85a00000000c68c000d8030c00000000030c8404c000030c84000000000c00c00000030ca0000000c30000c00000030c85a00000000c85a00000030c00000084000c,
  0x84068000084030000000030001a000000a000133006808404c00000008403000000004c0300a0000000000c00000000030000000030030000000030001a000000a006803000008400000000004c0300840000840300a000000008404c000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000085a30000000068001a680000d8001a30000030001a0000004c030068000030084068000000030030000084030000000085a300000000300000680000a000133000008403000000008403000000003003004c000000000c00000000030000000030030000000030001a000000a0068030000030001a68000068030000000085a300a0000000030030000000030000000030084000000030001a000000a0068030000000030000000085a3000000004c0300a0000000000c0000008404c0000000840300000000840000000000bc084030000030069a68000084030000000030030000000068030030000084084068000085a30000000030001a680000a000133006808404c00000008403000000004c0300a0000000000c00000000030000000030030000000030001a000000a0068030000084001a68000068030084000085a300a000000008404c000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000085a30000000068001a680000d8001a30000030001a0000004c030068000030084068000000030030000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000030084000000030001a000000a0068030000068001a68000068030000000085a300a0000000030030000000030000000030030000000030001a000000a006803000008404c000000085a300000000680300d8000068000c0000008404c000000084030000000030001a000000a0068030000030001a68000085a30000000085a300680000680300840000,
  0x840000000840000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a000000000008400000000004c0000840000840000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c000000000000084000000000000000000084000000000085a000000000000000000000a000130000008400000000008400000000000000004c0000000000000000000000000000000000000000000000000000a0000000000000000000000068000000000085a000a00000000000000000000000000000000840000000000000000000a0000000000000000000000085a0000000004c0000a000000000000000008404c0000000840000000000840000000000bc084000000000000000000084000000000000000000000000000000000084084000000085a000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a0000000000084000000000068000084000085a000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c0000000000000840000000000000000000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc0000000000000000000000000000000840000000000000000000a0000000000068000000000068000000000085a000a00000000000000000000000000000000000000000000000000000a000000000008404c000000085a000000000680000d800000000000000008404c0000000840000000000000000000000a0000000000000000000000085a00000000085a000000000000000840000,
  0x14084568001384030515301330015a1404d3a001533006808404c51404d38403051400134c0305a0001314014c14001314030514001330030515301330015a1404d3a006853130008401451404c04d3305853000840305a000131408454c001314031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c1400001403051404d385a30514001368015a6804d3d8015a3004c030015a1404d34c03056800003008456804c01403053000008403051404d385a3051530003001456804c0a001533000008403051404d38403051400133003054c001314014c14001314030514001330030515301330015a1404d3a0068530000030015a6804d369330515300085a305a0001314030530001314030514001330084515301330015a1404d3a006853000001403051404d385a3051400134d3305a004d314014c1400008404c51404d38403051400138401451404c0bc08453134c030069a6804c08403051400133003051404d36803053000008408456804d385a30515301330015a6804d3a001533006808404c51404d38403051400134c0305a0001314014c14001314030514001330030515301330015a1404d3a0068531300084015a6804d369330585300085a305a000131408454c001314031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c1400001403051404d385a30514001368015a6804d3d8015a3004c030015a1404d34c03056800003008456804c014030530000014031a6804d330030515301330069a6804c0a0014c3000008404c51404d38403051400134d3305bc04d314014c14000014030514001330084515301330015a1404d3a0068530000068015a6804d369330515300085a305a0001314030530001314030514001330030515301330015a1404d3a006853130008404c51404d385a305140013693305d804d368014c1400008404c51404d384030514001330015a1404d3a0068531300030015a6804d385a30514001385a3056804d3680305840013,
  0x840000000840000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a000000000008400000000004c0000840000840000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c000000000000084000000000000000000084000000000085a000000000000000000000a000130000008400000000008400000000000000004c0000000000000000000000000000000000000000000000000000a0000000000000000000000068000000000085a000a00000000000000000000000000000000840000000000000000000a0000000000000000000000085a0000000004c0000a000000000000000008404c0000000840000000000840000000000bc084000000000000000000084000000000000000000000000000000000084084000000085a000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a0000000000084000000000068000084000085a000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c0000000000000840000000000000000000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc0000000000000000000000000000000840000000000000000000a0000000000068000000000068000000000085a000a00000000000000000000000000000000000000000000000000000a000000000008404c000000085a000000000680000d800000000000000008404c0000000840000000000000000000000a0000000000000000000000085a00000000085a000000000000000840000,
  0x84068000084030000000030001a000000a000133006808404c00000008403000000004c0300a0000000000c00000000030000000030030000000030001a000000a006803000008400000000004c0300840000840300a000000008404c000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000085a30000000068001a680000d8001a30000030001a0000004c030068000030084068000000030030000084030000000085a300000000300000680000a000133000008403000000008403000000003003004c000000000c00000000030000000030030000000030001a000000a0068030000030001a68000068030000000085a300a0000000030030000000030000000030084000000030001a000000a0068030000000030000000085a3000000004c0300a0000000000c0000008404c0000000840300000000840000000000bc084030000030069a68000084030000000030030000000068030030000084084068000085a30000000030001a680000a000133006808404c00000008403000000004c0300a0000000000c00000000030000000030030000000030001a000000a0068030000084001a68000068030084000085a300a000000008404c000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000085a30000000068001a680000d8001a30000030001a0000004c030068000030084068000000030030000000031a68000030030000000030069a680000a0000c3000008404c00000008403000000004c0300bc000000000c00000000030000000030084000000030001a000000a0068030000068001a68000068030000000085a300a0000000030030000000030000000030030000000030001a000000a006803000008404c000000085a300000000680300d8000068000c0000008404c000000084030000000030001a000000a0068030000030001a68000085a30000000085a300680000680300840000,
  0x840000000840000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a000000000008400000000004c0000840000840000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c000000000000084000000000000000000084000000000085a000000000000000000000a000130000008400000000008400000000000000004c0000000000000000000000000000000000000000000000000000a0000000000000000000000068000000000085a000a00000000000000000000000000000000840000000000000000000a0000000000000000000000085a0000000004c0000a000000000000000008404c0000000840000000000840000000000bc084000000000000000000084000000000000000000000000000000000084084000000085a000000000000000000000a000130006808404c00000008400000000004c0000a00000000000000000000000000000000000000000000000000000a0000000000084000000000068000084000085a000a000000008404c0000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc000000000000000000000000000085a000000000680000000000d800000000000000000000004c0000000000000840000000000000000000000000000000000000000000000000000000a000000000008404c00000008400000000004c0000bc0000000000000000000000000000000840000000000000000000a0000000000068000000000068000000000085a000a00000000000000000000000000000000000000000000000000000a000000000008404c000000085a000000000680000d800000000000000008404c0000000840000000000000000000000a0000000000000000000000085a00000000085a000000000000000840000,
  0x65248410002710048b0120122d24841004846400044800194804841004a710048b01902011248b64000410000b48048410049964002710048b0000122d248410048464048448048b2d20041004991124a048000b10048b64000410048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a02c04841004a710048b0000202d200410049964049948048b2d248410048411248b48000b11248b10001964048b48000411248410003510048b0120192d248410001964000448000b4804841004a710048b01902011248b10000410000b48048410049964002710048b00000b2d248410048464048448048b2d200410049911248b48000b10048b64000410048b48000410048410001211248b00000b2d248410048464048448048b2c04841004a710048b00002011248b64000410000b0004a04804841004a710048b0000202d200410049910048448048b2d200410000410048b01902011248b10048410048b4804a065248410003510048b0120192d24841004996400044800194804841004a710048b01902011248b64000410000b48048410049964002710048b0000122d248410048464048448048b2d20041004991124a048000b10048b64000410048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a02c04841004a710048b0000202d200410049964049948048b2d248410048411248b48000b11248b10001964048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a010049964002711248b00000b2d248410048464048448048b2d200410049911248b48000b10048b64000410048b48000410049964002710048b0000122d248410048464048448048b4804841004a710048b0000201124a01000041000120004a04804841004a710048b0190202d248410048464048448048b2d248410049910048b00002010048b1004991004a0480484,
  0xb2c00002e700b2c000b01200b2c00002c00000002cb2d94802c00002e700b2c001902000b2c00000000000002c02c00002c00002e700b2c000b01200b2c00002c00002c02cb2c000b2c00002c000b2e02c000000b2c00000000002c02c000000b2e00002ee00b2c000b01200b2c00002c00000002cb2e04802c00002e700b2c000002000b2e00000000000122c02e00002c00002e700b2c000002000b2c00002c00002c02cb2c000b2c00002c000b2c02c000000b2c00002c00002c02c000000b2c00002f500b2c000b01900b2c00002c00000002cb2c04802c00002e700b2c001902000b2c00000000000002c02c00002c00002e700b2c000b00000b2c00002c00002c02cb2c000b2c00002c000b2c02c000000b2c00000000002c02c00000002c00002d200b2c000b00000b2c00002c00002c02cb2c00002c00002e700b2c000002000b2c00000000000002c02e04802c00002e700b2c000002000b2c00002c00002c02cb2c000b2c00002c000b2c001902000b2c00002c00002c02c02e000b2c00002f500b2c000b01900b2c00002c00000002cb2d94802c00002e700b2c001902000b2c00000000000002c02c00002c00002e700b2c000b01200b2c00002c00002c02cb2c000b2c00002c000b2e02c000000b2c00000000002c02c000000b2e00002ee00b2c000b01200b2c00002c00000002cb2e04802c00002e700b2c000002000b2e00000000000122c02e00002c00002e700b2c000002000b2c00002c00002c02cb2c000b2c00002c000b2c02c000000b2c00002c00002c02c000000b2e00002ee00b2c000b01200b2c00002c00000002cb2e04802c00002e700b2c000002000b2e00000000000122c02e00002c00002e700b2c000b00000b2c00002c00002c02cb2c000b2c00002c000b2c02c000000b2c00000000002c02c00000002c00002e700b2c000b01200b2c00002c00002c02cb2c04802c00002e700b2c000002000b2e00000000000122c02e04802c00002e700b2c001902000b2c00002c00002c02cb2c000b2c00002c000b2c000002000b2c00002c00002e02c02c0,
  0x64000000002700000b0000122c000000000064000000001948000000002700000b01902000000b64000000000b00000000001964002700000b0000122c000000000064000000000b2c000000001900002000000b00000b64000000000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b0000200000200000000000120000202c000000002700000b0000202c000000001964001900000b2c000000000000000b00000b00000b00001964000b00000000000000003500000b0000192c000000001964000000000b48000000002700000b01902000000b00000000000b00000000001964002700000b00000b2c000000000064000000000b2c000000001900000b00000b00000b64000000000b00000000000000001200000b00000b2c000000000064000000000b2c000000002700000b00002000000b64000000000b00002048000000002700000b0000202c000000001900000000000b2c000000000000000b01902000000b00000000000b00002064000000003500000b0000192c000000001964000000001948000000002700000b01902000000b64000000000b00000000001964002700000b0000122c000000000064000000000b2c000000001900002000000b00000b64000000000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b0000200000200000000000120000202c000000002700000b0000202c000000001964001900000b2c000000000000000b00000b00000b00001964000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b00002000002000000000001200002000001964002700000b00000b2c000000000064000000000b2c000000001900000b00000b00000b64000000000b00000000001964002700000b0000122c000000000064000000000b48000000002700000b00002000002000000000001200002048000000002700000b0190202c000000000064000000000b2c000000001900000b00002000000b000019000020000000,
  0x410000412700410010411200410000410000410010411948410000412700410011912000410000410000410010410000410000412700410010411200410000410000410010410000410000410000412010410000410000410000410010410000412000412e00410010411200410000410000410010412048410000412700410010412000412000410000411210412000410000412700410010412000410000410000410010410000410000410000410010410000410000410000410010410000410000413500410010411900410000410000410010410048410000412700410011912000410000410000410010410000410000412700410010410000410000410000410010410000410000410000410010410000410000410000410010410000410000411200410010410000410000410000410010410000410000412700410010412000410000410000410010412048410000412700410010412000410000410000410010410000410000410000410011912000410000410000410010412000410000413500410010411900410000410000410010411948410000412700410011912000410000410000410010410000410000412700410010411200410000410000410010410000410000410000412010410000410000410000410010410000412000412e00410010411200410000410000410010412048410000412700410010412000412000410000411210412000410000412700410010412000410000410000410010410000410000410000410010410000410000410000410010410000412000412e004100104112004100004100004100104120484100004127004100104120004120004100004112104120004100004127004100104100004100004100004100104100004100004100004100104100004100004100004100104100004100004127004100104112004100004100004100104100484100004127004100104120004120004100004112104120484100004127004100119120004100004100004100104100004100004100004100104120004100004100004120104100,
  0x65248410002710048b0120122d24841004846400044800194804841004a710048b01902011248b64000410000b48048410049964002710048b0000122d248410048464048448048b2d20041004991124a048000b10048b64000410048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a02c04841004a710048b0000202d200410049964049948048b2d248410048411248b48000b11248b10001964048b48000411248410003510048b0120192d248410001964000448000b4804841004a710048b01902011248b10000410000b48048410049964002710048b00000b2d248410048464048448048b2d200410049911248b48000b10048b64000410048b48000410048410001211248b00000b2d248410048464048448048b2c04841004a710048b00002011248b64000410000b0004a04804841004a710048b0000202d200410049910048448048b2d200410000410048b01902011248b10048410048b4804a065248410003510048b0120192d24841004996400044800194804841004a710048b01902011248b64000410000b48048410049964002710048b0000122d248410048464048448048b2d20041004991124a048000b10048b64000410048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a02c04841004a710048b0000202d200410049964049948048b2d248410048411248b48000b11248b10001964048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a010049964002711248b00000b2d248410048464048448048b2d200410049911248b48000b10048b64000410048b48000410049964002710048b0000122d248410048464048448048b4804841004a710048b0000201124a01000041000120004a04804841004a710048b0190202d248410048464048448048b2d248410049910048b00002010048b1004991004a0480484,
  0x2700000000001200000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000003500000000001900000000000000000000000048000000002700000001902000000000000000000000000000000000002700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000002700000000002000000000000000000000002048000000002700000000002000000000000000000000000000000000000000000001902000000000000000000000002000000000003500000000001900000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000002000002e000000000012000000000000000000000020480000000027000000000020000020000000000012000020000000000027000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000027000000000012000000000000000000000000480000000027000000000020000020000000000012000020480000000027000000019020000000000000000000000000000000000000000000000020000000000000000020000000,
  0x64000000002700000b0000122c000000000064000000001948000000002700000b01902000000b64000000000b00000000001964002700000b0000122c000000000064000000000b2c000000001900002000000b00000b64000000000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b0000200000200000000000120000202c000000002700000b0000202c000000001964001900000b2c000000000000000b00000b00000b00001964000b00000000000000003500000b0000192c000000001964000000000b48000000002700000b01902000000b00000000000b00000000001964002700000b00000b2c000000000064000000000b2c000000001900000b00000b00000b64000000000b00000000000000001200000b00000b2c000000000064000000000b2c000000002700000b00002000000b64000000000b00002048000000002700000b0000202c000000001900000000000b2c000000000000000b01902000000b00000000000b00002064000000003500000b0000192c000000001964000000001948000000002700000b01902000000b64000000000b00000000001964002700000b0000122c000000000064000000000b2c000000001900002000000b00000b64000000000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b0000200000200000000000120000202c000000002700000b0000202c000000001964001900000b2c000000000000000b00000b00000b00001964000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b00002000002000000000001200002000001964002700000b00000b2c000000000064000000000b2c000000001900000b00000b00000b64000000000b00000000001964002700000b0000122c000000000064000000000b48000000002700000b00002000002000000000001200002048000000002700000b0190202c000000000064000000000b2c000000001900000b00002000000b000019000020000000,
  0x2700000000001200000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000003500000000001900000000000000000000000048000000002700000001902000000000000000000000000000000000002700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000002700000000002000000000000000000000002048000000002700000000002000000000000000000000000000000000000000000001902000000000000000000000002000000000003500000000001900000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000002000002e000000000012000000000000000000000020480000000027000000000020000020000000000012000020000000000027000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000027000000000012000000000000000000000000480000000027000000000020000020000000000012000020480000000027000000019020000000000000000000000000000000000000000000000020000000000000000020000000,
  0x65248410002710048b0120122d24841004846400044800194804841004a710048b01902011248b64000410000b48048410049964002710048b0000122d248410048464048448048b2d20041004991124a048000b10048b64000410048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a02c04841004a710048b0000202d200410049964049948048b2d248410048411248b48000b11248b10001964048b48000411248410003510048b0120192d248410001964000448000b4804841004a710048b01902011248b10000410000b48048410049964002710048b00000b2d248410048464048448048b2d200410049911248b48000b10048b64000410048b48000410048410001211248b00000b2d248410048464048448048b2c04841004a710048b00002011248b64000410000b0004a04804841004a710048b0000202d200410049910048448048b2d200410000410048b01902011248b10048410048b4804a065248410003510048b0120192d24841004996400044800194804841004a710048b01902011248b64000410000b48048410049964002710048b0000122d248410048464048448048b2d20041004991124a048000b10048b64000410048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a02c04841004a710048b0000202d200410049964049948048b2d248410048411248b48000b11248b10001964048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a010049964002711248b00000b2d248410048464048448048b2d200410049911248b48000b10048b64000410048b48000410049964002710048b0000122d248410048464048448048b4804841004a710048b0000201124a01000041000120004a04804841004a710048b0190202d248410048464048448048b2d248410049910048b00002010048b1004991004a0480484,
  0xb2c00002e700b2c000b01200b2c00002c00000002cb2d94802c00002e700b2c001902000b2c00000000000002c02c00002c00002e700b2c000b01200b2c00002c00002c02cb2c000b2c00002c000b2e02c000000b2c00000000002c02c000000b2e00002ee00b2c000b01200b2c00002c00000002cb2e04802c00002e700b2c000002000b2e00000000000122c02e00002c00002e700b2c000002000b2c00002c00002c02cb2c000b2c00002c000b2c02c000000b2c00002c00002c02c000000b2c00002f500b2c000b01900b2c00002c00000002cb2c04802c00002e700b2c001902000b2c00000000000002c02c00002c00002e700b2c000b00000b2c00002c00002c02cb2c000b2c00002c000b2c02c000000b2c00000000002c02c00000002c00002d200b2c000b00000b2c00002c00002c02cb2c00002c00002e700b2c000002000b2c00000000000002c02e04802c00002e700b2c000002000b2c00002c00002c02cb2c000b2c00002c000b2c001902000b2c00002c00002c02c02e000b2c00002f500b2c000b01900b2c00002c00000002cb2d94802c00002e700b2c001902000b2c00000000000002c02c00002c00002e700b2c000b01200b2c00002c00002c02cb2c000b2c00002c000b2e02c000000b2c00000000002c02c000000b2e00002ee00b2c000b01200b2c00002c00000002cb2e04802c00002e700b2c000002000b2e00000000000122c02e00002c00002e700b2c000002000b2c00002c00002c02cb2c000b2c00002c000b2c02c000000b2c00002c00002c02c000000b2e00002ee00b2c000b01200b2c00002c00000002cb2e04802c00002e700b2c000002000b2e00000000000122c02e00002c00002e700b2c000b00000b2c00002c00002c02cb2c000b2c00002c000b2c02c000000b2c00000000002c02c00000002c00002e700b2c000b01200b2c00002c00002c02cb2c04802c00002e700b2c000002000b2e00000000000122c02e04802c00002e700b2c001902000b2c00002c00002c02cb2c000b2c00002c000b2c000002000b2c00002c00002e02c02c0,
  0x64000000002700000b0000122c000000000064000000001948000000002700000b01902000000b64000000000b00000000001964002700000b0000122c000000000064000000000b2c000000001900002000000b00000b64000000000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b0000200000200000000000120000202c000000002700000b0000202c000000001964001900000b2c000000000000000b00000b00000b00001964000b00000000000000003500000b0000192c000000001964000000000b48000000002700000b01902000000b00000000000b00000000001964002700000b00000b2c000000000064000000000b2c000000001900000b00000b00000b64000000000b00000000000000001200000b00000b2c000000000064000000000b2c000000002700000b00002000000b64000000000b00002048000000002700000b0000202c000000001900000000000b2c000000000000000b01902000000b00000000000b00002064000000003500000b0000192c000000001964000000001948000000002700000b01902000000b64000000000b00000000001964002700000b0000122c000000000064000000000b2c000000001900002000000b00000b64000000000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b0000200000200000000000120000202c000000002700000b0000202c000000001964001900000b2c000000000000000b00000b00000b00001964000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b00002000002000000000001200002000001964002700000b00000b2c000000000064000000000b2c000000001900000b00000b00000b64000000000b00000000001964002700000b0000122c000000000064000000000b48000000002700000b00002000002000000000001200002048000000002700000b0190202c000000000064000000000b2c000000001900000b00002000000b000019000020000000,
  0x2700000000001200000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000003500000000001900000000000000000000000048000000002700000001902000000000000000000000000000000000002700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000002700000000002000000000000000000000002048000000002700000000002000000000000000000000000000000000000000000001902000000000000000000000002000000000003500000000001900000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000002000002e000000000012000000000000000000000020480000000027000000000020000020000000000012000020000000000027000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000027000000000012000000000000000000000000480000000027000000000020000020000000000012000020480000000027000000019020000000000000000000000000000000000000000000000020000000000000000020000000,
  0x65248410002710048b0120122d24841004846400044800194804841004a710048b01902011248b64000410000b48048410049964002710048b0000122d248410048464048448048b2d20041004991124a048000b10048b64000410048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a02c04841004a710048b0000202d200410049964049948048b2d248410048411248b48000b11248b10001964048b48000411248410003510048b0120192d248410001964000448000b4804841004a710048b01902011248b10000410000b48048410049964002710048b00000b2d248410048464048448048b2d200410049911248b48000b10048b64000410048b48000410048410001211248b00000b2d248410048464048448048b2c04841004a710048b00002011248b64000410000b0004a04804841004a710048b0000202d200410049910048448048b2d200410000410048b01902011248b10048410048b4804a065248410003510048b0120192d24841004996400044800194804841004a710048b01902011248b64000410000b48048410049964002710048b0000122d248410048464048448048b2d20041004991124a048000b10048b64000410048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a02c04841004a710048b0000202d200410049964049948048b2d248410048411248b48000b11248b10001964048b4800041124a010002e11248b0120122d20041000041000044800204804841004a710048b0000201124a01000041000120004a010049964002711248b00000b2d248410048464048448048b2d200410049911248b48000b10048b64000410048b48000410049964002710048b0000122d248410048464048448048b4804841004a710048b0000201124a01000041000120004a04804841004a710048b0190202d248410048464048448048b2d248410049910048b00002010048b1004991004a0480484,
  0x2700000000001200000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000003500000000001900000000000000000000000048000000002700000001902000000000000000000000000000000000002700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000002700000000002000000000000000000000002048000000002700000000002000000000000000000000000000000000000000000001902000000000000000000000002000000000003500000000001900000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000002000002e000000000012000000000000000000000020480000000027000000000020000020000000000012000020000000000027000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000027000000000012000000000000000000000000480000000027000000000020000020000000000012000020480000000027000000019020000000000000000000000000000000000000000000000020000000000000000020000000,
  0x64000000002700000b0000122c000000000064000000001948000000002700000b01902000000b64000000000b00000000001964002700000b0000122c000000000064000000000b2c000000001900002000000b00000b64000000000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b0000200000200000000000120000202c000000002700000b0000202c000000001964001900000b2c000000000000000b00000b00000b00001964000b00000000000000003500000b0000192c000000001964000000000b48000000002700000b01902000000b00000000000b00000000001964002700000b00000b2c000000000064000000000b2c000000001900000b00000b00000b64000000000b00000000000000001200000b00000b2c000000000064000000000b2c000000002700000b00002000000b64000000000b00002048000000002700000b0000202c000000001900000000000b2c000000000000000b01902000000b00000000000b00002064000000003500000b0000192c000000001964000000001948000000002700000b01902000000b64000000000b00000000001964002700000b0000122c000000000064000000000b2c000000001900002000000b00000b64000000000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b0000200000200000000000120000202c000000002700000b0000202c000000001964001900000b2c000000000000000b00000b00000b00001964000b00000000002000002e00000b0000122c000000000000000000002048000000002700000b00002000002000000000001200002000001964002700000b00000b2c000000000064000000000b2c000000001900000b00000b00000b64000000000b00000000001964002700000b0000122c000000000064000000000b48000000002700000b00002000002000000000001200002048000000002700000b0190202c000000000064000000000b2c000000001900000b00002000000b000019000020000000,
  0x2700000000001200000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000003500000000001900000000000000000000000048000000002700000001902000000000000000000000000000000000002700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000002700000000002000000000000000000000002048000000002700000000002000000000000000000000000000000000000000000001902000000000000000000000002000000000003500000000001900000000000000000000001948000000002700000001902000000000000000000000000000000000002700000000001200000000000000000000000000000000000000002000000000000000000000000000000000002000002e00000000001200000000000000000000002048000000002700000000002000002000000000001200002000000000002700000000002000000000000000000000000000000000000000000000000000000000000000000000000000002000002e000000000012000000000000000000000020480000000027000000000020000020000000000012000020000000000027000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000027000000000012000000000000000000000000480000000027000000000020000020000000000012000020480000000027000000019020000000000000000000000000000000000000000000000020000000000000000020000000,
  0x344300360a00a4514430ca44a0030030d100301844329f00300300361f00a45101f0d144a4660030df00344a01828300344301f60a00a46d4430ca44a0030030d10034434432830110180030ca44a4664430ca00a4510030ca00346d0030c30034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f4436030030180df00a4660180df0110030030d100300345828344a0030030d144a4664430d100a46d0030d101f4514430df0184430030ca00a4664430ca44a0180030ca00301844328300300300360a00a45101f0d844a45f0030df00345f01828300344301f60a00a46d4430ca44a0030030d10034434432830110030030ca00a4510030ca00a46600360a01847b0030c30034430030ca00a46d4430ca44a0030030d10034434432836030030180df00a4660180df44a4660030ca00345f01f45800300300361f00a4510030ca0110180030ca0034434432834510180030d800a45101f0d801f4740030d100345f4430c301844300360a00a4664430ca44a0180030d100301844329f00300300361f00a45101f0d844a4660030df00345f01828300344301f60a00a46d4430ca44a0030030d10034434432830110180030ca44a4664430ca00a46600360a01847b0030c30034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f4436030030180df00a4660180df0110030030d100300345828344a0030030d144a4664430d100a46d0030d101f4514430df0034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f44300344301f60a00a46d4430ca44a0030030d10034434432830110030030d144a4660030d100a46600360a01847b0030c300344301f60a00a46d4430ca44a0030030d100344344328360300301861f00a4660180ca44a4660030df00344a01f44300300300361f00a45101f0d844a0030030d100344344328344a0180030d100a4660180df00a4660030d1003466443603,
  0x28000000028029128000028000000001100028028001f00000000001f28029129f0112802a600001f00028000000000028001f0002802ad2800002800000000110002802800002910000000002802a62800002802910000000002ad00000000028000000029f2b428000029100000001800028028001f00000000001f2802912800002802a600000000028001f44060000000001f2802a628001f2910000000110002802800002800000000112802a62800112802ad00001101f29128001f0002800000002802a628000028000000000000028028000000000000000028029129f01828029f00001f00029f00000000028001f0002802ad2800002800000000110002802800002910000000002802912800002802a60000000002bb0000000002800000002802ad28000028000000001100028028000060000000001f2802a628001f2802a600000000029f01f44000000000001f28029128000029100000000000028028000029100000001828029129f01829f2b400001100029f2800000002800000002802a628000028000000001100028028001f00000000001f28029129f0182802a600001f00029f00000000028001f0002802ad2800002800000000110002802800002910000000002802a62800002802a60000000002bb00000000028000000029f2b428000029100000001800028028001f00000000001f2802912800002802a600000000028001f44060000000001f2802a628001f2910000000110002802800002800000000112802a62800112802ad00001101f29128001f00028000000029f2b428000029100000001800028028001f00000000001f2802912800002802a600000000028001f44000028001f0002802ad2800002800000000110002802800002910000000112802a62800112802a60000000002bb00000000028001f0002802ad28000028000000001100028028000060000000001f2802a62800002802a600001f00028001f44000000000001f28029129f0182800000000110002802800002800000000112802a628001f2802a60000110002a6280000,
  0x60a00a01100000a00a00000001100001800029f00000000061f00a01101f01100a02600001f00000a01828000000001f60a00a02d00000a00a00000001100000000028001101800000a00a02600000a00a01100000a00002d00000000000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44060000001801f00a02601801f01100000001100000001828000a00000001100a02600001100a02d00001101f01100001f01800000000a00a02600000a00a01800000a00001800028000000000060a00a01101f01800a01f00001f00001f01828000000001f60a00a02d00000a00a00000001100000000028001100000000a00a01100000a00a02600060a01803b00000000000000000a00a02d00000a00a00000001100000000028060000001801f00a02601801f00a02600000a00001f01f45800000000061f00a01100000a01101800000a00000000028001101800001800a01101f01801f03400001100001f00000001800000060a00a02600000a00a01800001100001800029f00000000061f00a01101f01800a02600001f00001f01828000000001f60a00a02d00000a00a00000001100000000028001101800000a00a02600000a00a02600060a01803b00000000000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44060000001801f00a02601801f01100000001100000001828000a00000001100a02600001100a02d00001101f01100001f00000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44000000001f60a00a02d00000a00a00000001100000000028001100000001100a02600001100a02600060a01803b00000000000001f60a00a02d00000a00a00000001100000000028060000001861f00a02601800a00a02600001f00000a01f44000000000061f00a01101f01800a00000001100000000028000a01800001100a02601801f00a026000011000026000600,
  0xc00c00c00000c00d10c00000c00c00c00110c00c00c001f0c00c00c001f0c00d10df0110c00e60c001f0c00c00c00000c00c00df0000c00ed0c00000c00c00c00110c00c00c00000d10c00c00000c00e60c00000c00d10c00000c00ed0c00000c00c00c00000df0f40c00000d10c00c00180c00c00c001f0c00c00c001f0c00d10c00000c00e60c00000c00c00df4406000c00c001f0c00e60c001f0d10c00c00110c00c00c00000c00c00c00110c00e60c00110c00ed0c00110df0d10c001f0c00c00c00000c00e60c00000c00c00c00000c00c00c00000c00c00c00000c00d10df0180c00df0c001f0c00df0c00000c00c00df0000c00ed0c00000c00c00c00110c00c00c00000d10c00c00000c00d10c00000c00e60c00000c00fb0c00000c00c00c00000c00ed0c00000c00c00c00110c00c00c00006000c00c001f0c00e60c001f0c00e60c00000c00df0df4400c00c00c001f0c00d10c00000d10c00c00000c00c00c00000d10c00c00180c00d10df0180df0f40c00110c00df0c00000c00c00c00000c00e60c00000c00c00c00110c00c00c001f0c00c00c001f0c00d10df0180c00e60c001f0c00df0c00000c00c00df0000c00ed0c00000c00c00c00110c00c00c00000d10c00c00000c00e60c00000c00e60c00000c00fb0c00000c00c00c00000df0f40c00000d10c00c00180c00c00c001f0c00c00c001f0c00d10c00000c00e60c00000c00c00df4406000c00c001f0c00e60c001f0d10c00c00110c00c00c00000c00c00c00110c00e60c00110c00ed0c00110df0d10c001f0c00c00c00000df0f40c00000d10c00c00180c00c00c001f0c00c00c001f0c00d10c00000c00e60c00000c00c00df4400c00c00df0000c00ed0c00000c00c00c00110c00c00c00000d10c00c00110c00e60c00110c00e60c00000c00fb0c00000c00c00df0000c00ed0c00000c00c00c00110c00c00c00006000c00c001f0c00e60c00000c00e60c001f0c00c00df4400c00c00c001f0c00d10df0180c00c00c00110c00c00c00000c00c00c00110c00e60c001f0c00e60c00110c00e60c0000,
  0x344300360a00a4514430ca44a0030030d100301844329f00300300361f00a45101f0d144a4660030df00344a01828300344301f60a00a46d4430ca44a0030030d10034434432830110180030ca44a4664430ca00a4510030ca00346d0030c30034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f4436030030180df00a4660180df0110030030d100300345828344a0030030d144a4664430d100a46d0030d101f4514430df0184430030ca00a4664430ca44a0180030ca00301844328300300300360a00a45101f0d844a45f0030df00345f01828300344301f60a00a46d4430ca44a0030030d10034434432830110030030ca00a4510030ca00a46600360a01847b0030c30034430030ca00a46d4430ca44a0030030d10034434432836030030180df00a4660180df44a4660030ca00345f01f45800300300361f00a4510030ca0110180030ca0034434432834510180030d800a45101f0d801f4740030d100345f4430c301844300360a00a4664430ca44a0180030d100301844329f00300300361f00a45101f0d844a4660030df00345f01828300344301f60a00a46d4430ca44a0030030d10034434432830110180030ca44a4664430ca00a46600360a01847b0030c30034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f4436030030180df00a4660180df0110030030d100300345828344a0030030d144a4664430d100a46d0030d101f4514430df0034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f44300344301f60a00a46d4430ca44a0030030d10034434432830110030030d144a4660030d100a46600360a01847b0030c300344301f60a00a46d4430ca44a0030030d100344344328360300301861f00a4660180ca44a4660030df00344a01f44300300300361f00a45101f0d844a0030030d100344344328344a0180030d100a4660180df00a4660030d1003466443603,
  0x1100000000000000001100000000001f00000000001f00001101f01100002600001f00000000000000000001f00000002d00000000000000001100000000000001100000000000002600000000001100000000002d00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000000002600000000000000000000000000000000000000000000001101f01800001f00001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000001100000000002600000000003b00000000000000000000002d00000000000000001100000000000060000000001f00002600001f00002600000000001f01f44000000000001f00001100000001100000000000000000000001100000001800001101f01801f03400001100001f00000000000000000000002600000000000000001100000000001f00000000001f00001101f01800002600001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000002600000000002600000000003b00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44000000001f00000002d00000000000000001100000000000001100000001100002600001100002600000000003b00000000000001f00000002d00000000000000001100000000000060000000001f00002600000000002600001f00000001f44000000000001f00001101f01800000000001100000000000000000000001100002600001f000026000011000026000000,
  0x60a00a01100000a00a00000001100001800029f00000000061f00a01101f01100a02600001f00000a01828000000001f60a00a02d00000a00a00000001100000000028001101800000a00a02600000a00a01100000a00002d00000000000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44060000001801f00a02601801f01100000001100000001828000a00000001100a02600001100a02d00001101f01100001f01800000000a00a02600000a00a01800000a00001800028000000000060a00a01101f01800a01f00001f00001f01828000000001f60a00a02d00000a00a00000001100000000028001100000000a00a01100000a00a02600060a01803b00000000000000000a00a02d00000a00a00000001100000000028060000001801f00a02601801f00a02600000a00001f01f45800000000061f00a01100000a01101800000a00000000028001101800001800a01101f01801f03400001100001f00000001800000060a00a02600000a00a01800001100001800029f00000000061f00a01101f01800a02600001f00001f01828000000001f60a00a02d00000a00a00000001100000000028001101800000a00a02600000a00a02600060a01803b00000000000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44060000001801f00a02601801f01100000001100000001828000a00000001100a02600001100a02d00001101f01100001f00000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44000000001f60a00a02d00000a00a00000001100000000028001100000001100a02600001100a02600060a01803b00000000000001f60a00a02d00000a00a00000001100000000028060000001861f00a02601800a00a02600001f00000a01f44000000000061f00a01101f01800a00000001100000000028000a01800001100a02601801f00a026000011000026000600,
  0x1100000000000000001100000000001f00000000001f00001101f01100002600001f00000000000000000001f00000002d00000000000000001100000000000001100000000000002600000000001100000000002d00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000000002600000000000000000000000000000000000000000000001101f01800001f00001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000001100000000002600000000003b00000000000000000000002d00000000000000001100000000000060000000001f00002600001f00002600000000001f01f44000000000001f00001100000001100000000000000000000001100000001800001101f01801f03400001100001f00000000000000000000002600000000000000001100000000001f00000000001f00001101f01800002600001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000002600000000002600000000003b00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44000000001f00000002d00000000000000001100000000000001100000001100002600001100002600000000003b00000000000001f00000002d00000000000000001100000000000060000000001f00002600000000002600001f00000001f44000000000001f00001101f01800000000001100000000000000000000001100002600001f000026000011000026000000,
  0x344300360a00a4514430ca44a0030030d100301844329f00300300361f00a45101f0d144a4660030df00344a01828300344301f60a00a46d4430ca44a0030030d10034434432830110180030ca44a4664430ca00a4510030ca00346d0030c30034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f4436030030180df00a4660180df0110030030d100300345828344a0030030d144a4664430d100a46d0030d101f4514430df0184430030ca00a4664430ca44a0180030ca00301844328300300300360a00a45101f0d844a45f0030df00345f01828300344301f60a00a46d4430ca44a0030030d10034434432830110030030ca00a4510030ca00a46600360a01847b0030c30034430030ca00a46d4430ca44a0030030d10034434432836030030180df00a4660180df44a4660030ca00345f01f45800300300361f00a4510030ca0110180030ca0034434432834510180030d800a45101f0d801f4740030d100345f4430c301844300360a00a4664430ca44a0180030d100301844329f00300300361f00a45101f0d844a4660030df00345f01828300344301f60a00a46d4430ca44a0030030d10034434432830110180030ca44a4664430ca00a46600360a01847b0030c30034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f4436030030180df00a4660180df0110030030d100300345828344a0030030d144a4664430d100a46d0030d101f4514430df0034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f44300344301f60a00a46d4430ca44a0030030d10034434432830110030030d144a4660030d100a46600360a01847b0030c300344301f60a00a46d4430ca44a0030030d100344344328360300301861f00a4660180ca44a4660030df00344a01f44300300300361f00a45101f0d844a0030030d100344344328344a0180030d100a4660180df00a4660030d1003466443603,
  0x28000000028029128000028000000001100028028001f00000000001f28029129f0112802a600001f00028000000000028001f0002802ad2800002800000000110002802800002910000000002802a62800002802910000000002ad00000000028000000029f2b428000029100000001800028028001f00000000001f2802912800002802a600000000028001f44060000000001f2802a628001f2910000000110002802800002800000000112802a62800112802ad00001101f29128001f0002800000002802a628000028000000000000028028000000000000000028029129f01828029f00001f00029f00000000028001f0002802ad2800002800000000110002802800002910000000002802912800002802a60000000002bb0000000002800000002802ad28000028000000001100028028000060000000001f2802a628001f2802a600000000029f01f44000000000001f28029128000029100000000000028028000029100000001828029129f01829f2b400001100029f2800000002800000002802a628000028000000001100028028001f00000000001f28029129f0182802a600001f00029f00000000028001f0002802ad2800002800000000110002802800002910000000002802a62800002802a60000000002bb00000000028000000029f2b428000029100000001800028028001f00000000001f2802912800002802a600000000028001f44060000000001f2802a628001f2910000000110002802800002800000000112802a62800112802ad00001101f29128001f00028000000029f2b428000029100000001800028028001f00000000001f2802912800002802a600000000028001f44000028001f0002802ad2800002800000000110002802800002910000000112802a62800112802a60000000002bb00000000028001f0002802ad28000028000000001100028028000060000000001f2802a62800002802a600001f00028001f44000000000001f28029129f0182800000000110002802800002800000000112802a628001f2802a60000110002a6280000,
  0x60a00a01100000a00a00000001100001800029f00000000061f00a01101f01100a02600001f00000a01828000000001f60a00a02d00000a00a00000001100000000028001101800000a00a02600000a00a01100000a00002d00000000000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44060000001801f00a02601801f01100000001100000001828000a00000001100a02600001100a02d00001101f01100001f01800000000a00a02600000a00a01800000a00001800028000000000060a00a01101f01800a01f00001f00001f01828000000001f60a00a02d00000a00a00000001100000000028001100000000a00a01100000a00a02600060a01803b00000000000000000a00a02d00000a00a00000001100000000028060000001801f00a02601801f00a02600000a00001f01f45800000000061f00a01100000a01101800000a00000000028001101800001800a01101f01801f03400001100001f00000001800000060a00a02600000a00a01800001100001800029f00000000061f00a01101f01800a02600001f00001f01828000000001f60a00a02d00000a00a00000001100000000028001101800000a00a02600000a00a02600060a01803b00000000000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44060000001801f00a02601801f01100000001100000001828000a00000001100a02600001100a02d00001101f01100001f00000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44000000001f60a00a02d00000a00a00000001100000000028001100000001100a02600001100a02600060a01803b00000000000001f60a00a02d00000a00a00000001100000000028060000001861f00a02601800a00a02600001f00000a01f44000000000061f00a01101f01800a00000001100000000028000a01800001100a02601801f00a026000011000026000600,
  0x1100000000000000001100000000001f00000000001f00001101f01100002600001f00000000000000000001f00000002d00000000000000001100000000000001100000000000002600000000001100000000002d00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000000002600000000000000000000000000000000000000000000001101f01800001f00001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000001100000000002600000000003b00000000000000000000002d00000000000000001100000000000060000000001f00002600001f00002600000000001f01f44000000000001f00001100000001100000000000000000000001100000001800001101f01801f03400001100001f00000000000000000000002600000000000000001100000000001f00000000001f00001101f01800002600001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000002600000000002600000000003b00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44000000001f00000002d00000000000000001100000000000001100000001100002600001100002600000000003b00000000000001f00000002d00000000000000001100000000000060000000001f00002600000000002600001f00000001f44000000000001f00001101f01800000000001100000000000000000000001100002600001f000026000011000026000000,
  0x344300360a00a4514430ca44a0030030d100301844329f00300300361f00a45101f0d144a4660030df00344a01828300344301f60a00a46d4430ca44a0030030d10034434432830110180030ca44a4664430ca00a4510030ca00346d0030c30034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f4436030030180df00a4660180df0110030030d100300345828344a0030030d144a4664430d100a46d0030d101f4514430df0184430030ca00a4664430ca44a0180030ca00301844328300300300360a00a45101f0d844a45f0030df00345f01828300344301f60a00a46d4430ca44a0030030d10034434432830110030030ca00a4510030ca00a46600360a01847b0030c30034430030ca00a46d4430ca44a0030030d10034434432836030030180df00a4660180df44a4660030ca00345f01f45800300300361f00a4510030ca0110180030ca0034434432834510180030d800a45101f0d801f4740030d100345f4430c301844300360a00a4664430ca44a0180030d100301844329f00300300361f00a45101f0d844a4660030df00345f01828300344301f60a00a46d4430ca44a0030030d10034434432830110180030ca44a4664430ca00a46600360a01847b0030c30034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f4436030030180df00a4660180df0110030030d100300345828344a0030030d144a4664430d100a46d0030d101f4514430df0034430030ca01f4744430ca4510180030d800301845829f00300300361f00a4510030ca44a4660030ca00344a01f44300344301f60a00a46d4430ca44a0030030d10034434432830110030030d144a4660030d100a46600360a01847b0030c300344301f60a00a46d4430ca44a0030030d100344344328360300301861f00a4660180ca44a4660030df00344a01f44300300300361f00a45101f0d844a0030030d100344344328344a0180030d100a4660180df00a4660030d1003466443603,
  0x1100000000000000001100000000001f00000000001f00001101f01100002600001f00000000000000000001f00000002d00000000000000001100000000000001100000000000002600000000001100000000002d00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000000002600000000000000000000000000000000000000000000001101f01800001f00001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000001100000000002600000000003b00000000000000000000002d00000000000000001100000000000060000000001f00002600001f00002600000000001f01f44000000000001f00001100000001100000000000000000000001100000001800001101f01801f03400001100001f00000000000000000000002600000000000000001100000000001f00000000001f00001101f01800002600001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000002600000000002600000000003b00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44000000001f00000002d00000000000000001100000000000001100000001100002600001100002600000000003b00000000000001f00000002d00000000000000001100000000000060000000001f00002600000000002600001f00000001f44000000000001f00001101f01800000000001100000000000000000000001100002600001f000026000011000026000000,
  0x60a00a01100000a00a00000001100001800029f00000000061f00a01101f01100a02600001f00000a01828000000001f60a00a02d00000a00a00000001100000000028001101800000a00a02600000a00a01100000a00002d00000000000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44060000001801f00a02601801f01100000001100000001828000a00000001100a02600001100a02d00001101f01100001f01800000000a00a02600000a00a01800000a00001800028000000000060a00a01101f01800a01f00001f00001f01828000000001f60a00a02d00000a00a00000001100000000028001100000000a00a01100000a00a02600060a01803b00000000000000000a00a02d00000a00a00000001100000000028060000001801f00a02601801f00a02600000a00001f01f45800000000061f00a01100000a01101800000a00000000028001101800001800a01101f01801f03400001100001f00000001800000060a00a02600000a00a01800001100001800029f00000000061f00a01101f01800a02600001f00001f01828000000001f60a00a02d00000a00a00000001100000000028001101800000a00a02600000a00a02600060a01803b00000000000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44060000001801f00a02601801f01100000001100000001828000a00000001100a02600001100a02d00001101f01100001f00000000000a01f03400000a01101800001800001801829f00000000061f00a01100000a00a02600000a00000a01f44000000001f60a00a02d00000a00a00000001100000000028001100000001100a02600001100a02600060a01803b00000000000001f60a00a02d00000a00a00000001100000000028060000001861f00a02601800a00a02600001f00000a01f44000000000061f00a01101f01800a00000001100000000028000a01800001100a02601801f00a026000011000026000600,
  0x1100000000000000001100000000001f00000000001f00001101f01100002600001f00000000000000000001f00000002d00000000000000001100000000000001100000000000002600000000001100000000002d00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000000002600000000000000000000000000000000000000000000001101f01800001f00001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000001100000000002600000000003b00000000000000000000002d00000000000000001100000000000060000000001f00002600001f00002600000000001f01f44000000000001f00001100000001100000000000000000000001100000001800001101f01801f03400001100001f00000000000000000000002600000000000000001100000000001f00000000001f00001101f01800002600001f00001f00000000000001f00000002d00000000000000001100000000000001100000000000002600000000002600000000003b00000000000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44060000000001f00002600001f01100000001100000000000000000000001100002600001100002d00001101f01100001f00000000000001f03400000001100000001800000000001f00000000001f00001100000000002600000000000001f44000000001f00000002d00000000000000001100000000000001100000001100002600001100002600000000003b00000000000001f00000002d00000000000000001100000000000060000000001f00002600000000002600001f00000001f44000000000001f00001101f01800000000001100000000000000000000001100002600001f000026000011000026000000,
  0x822400824009422505c909078241008224009e5c02505c05d72400827809422505c9080cc27900977800825c04020970827900824009422505c90902424100822400975c0789090402250082240b177905c90804022500822400822502420800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420805de2400825c04172505c97804025d00822405c25c02505d0782410082240cc27905de5c07822500822400822507820800827800822404172505c90802422500822400825c02500805d72400822409422505c9780e827900977800825c04020970822500824005c22505c90902424100822400975c0789090402410082240b172505c908041725009e2400827902427800827800824007822505c90907824100822400975c07890905de2400825c04022505c9080b172500822400825c05c20805c22400822404022505c90804022500822405c25c07895d02422500822409422505c97809422500822400827902570800827800824009572505c909078241008224009e5c02505c05d72400827809422505c9780e827900977800825c04020970827900824009422505c90902424100822400975c0789090402410082240b177905c908041725009e2400827902427800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420805de2400825c04172505c97804025d00822405c25c02505d0782410082240cc27905de5c07822500822400822507820800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420800827900824007822505c90907824100822400975c07890904025d0082240b172505c908041725009e2400827902427800827900824009422505c90902424100822400975c07890905de2400824004172505c9780b177905c22400825c04020805d72400827809422505c97807824100822400975c07890907824100822404172505c9780957250082240082790782080,
  0x900040094000900000978040900000001e000010009000009000780940009000009cc0789000780000000400017000789000400940009000009000409000000000000780009400009000000b0078900000940000900000000000900000000000900000094000900000900000900000001e000010009000009000000400009000009b0078900000000000000000001e0090005c04000090007894005c9000000000000010009780409000000cc078901e009780009000000000009780000000789000000400009000009000009000000000000010009000009000000940009000789e807890007800000004000170000090004005c0009000009000409000000000000780009400409000000b0000900000940000901e00000078900078000078900040078000900000978040900000000000078000901e0090005c0400009000009b000090000000000005c000000000900000040000900000940000900000000000078000900000900000094000900078994000900000000078900000000078900040094000900000978040900000001e000010009000009000780940009000789e80789000780000000400017000789000400940009000009000409000000000000780009400409000000b0078900000940000901e00000078900078000000900000094000900000900000900000001e000010009000009000000400009000009b0078900000000000000000001e0090005c04000090007894005c9000000000000010009780409000000cc078901e00978000900000000000978000000000900000094000900000900000900000001e000010009000009000000400009000009b007890000000000000000000007890004007800090000097804090000000000007800094005c9000000b0000900000940000901e00000078900078000078900040094000900000900040900000000000078000901e009000400400009000789b00789000000000000400000000009000780940009000789780409000000000000780009780409000000400009000789940009000000000789780000,
  0x2400004009402405c900078040000024001e5c02505c05d72400007809402405c9000cc07800177800005c04000170007800004009402405c90002404000002400175c0789000400240000240b177805c90004002400002400002402400000002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400005de2400005c04172405c97804005c00002405c05c02505c0780400000240cc07805de5c07802400002400002407800000007800002404172405c90002402400002400005c02500005d72400002409402405c9780e807800177800005c04000170002400004005c02405c90002404000002400175c0789000400400000240b172405c900041724001e2400007802407800007800004007802405c90007804000002400175c07890005de2400005c04002405c9000b172400002400005c05c00005c02400002404002405c90004002400002405c05c07895c02402400002409402405c97809402400002400007802570000007800004009572405c900078040000024001e5c02505c05d72400007809402405c9780e807800177800005c04000170007800004009402405c90002404000002400175c0789000400400000240b177805c900041724001e2400007802407800002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400005de2400005c04172405c97804005c00002405c05c02505c0780400000240cc07805de5c07802400002400002407800000002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400000007800004007802405c90007804000002400175c07890004005c0000240b172405c900041724001e2400007802407800007800004009402405c90002404000002400175c07890005de2400004004172405c9780b177805c02400005c04000005d72400007809402405c97807804000002400175c07890007804000002404172405c9780957240000240000780780000,
  0x200040294000200000278040200000201e002010002000002000782940002000002cc0782000782000002400017000782000402940002000002000402000002000002780002400002000002b0078200000240000200000200000200000200000200000294000200000200000200000201e002010002000002000002400002000002b0078200000200000200000201e0020005c24000020007824005c2000002000002010002780402000002cc078201e002780002000002000002780002000782000002400002000002000002000002000002010002000002000002940002000782e807820007820000024000170000020004025c0002000002000402000002000002780002400402000002b0000200000240000201e00200078200078200078200040278000200000278040200000200000278000201e0020005c2400002000002b000020000020000025c000200000200000240000200000240000200000200000278000200000200000294000200078294000200000200078200000200078200040294000200000278040200000201e002010002000002000782940002000782e80782000782000002400017000782000402940002000002000402000002000002780002400402000002b0078200000240000201e00200078200078200000200000294000200000200000200000201e002010002000002000002400002000002b0078200000200000200000201e0020005c24000020007824005c2000002000002010002780402000002cc078201e00278000200000200000278000200000200000294000200000200000200000201e002010002000002000002400002000002b007820000020000020000020007820004027800020000027804020000020000027800024005c2000002b0000200000240000201e00200078200078200078200040294000200000200040200000200000278000201e002000402400002000782b00782000002000002400002000002000782940002000782780402000002000002780002780402000002400002000782940002000002000782780002,
  0x822400824009422505c909078241008224009e5c02505c05d72400827809422505c9080cc27900977800825c04020970827900824009422505c90902424100822400975c0789090402250082240b177905c90804022500822400822502420800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420805de2400825c04172505c97804025d00822405c25c02505d0782410082240cc27905de5c07822500822400822507820800827800822404172505c90802422500822400825c02500805d72400822409422505c9780e827900977800825c04020970822500824005c22505c90902424100822400975c0789090402410082240b172505c908041725009e2400827902427800827800824007822505c90907824100822400975c07890905de2400825c04022505c9080b172500822400825c05c20805c22400822404022505c90804022500822405c25c07895d02422500822409422505c97809422500822400827902570800827800824009572505c909078241008224009e5c02505c05d72400827809422505c9780e827900977800825c04020970827900824009422505c90902424100822400975c0789090402410082240b177905c908041725009e2400827902427800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420805de2400825c04172505c97804025d00822405c25c02505d0782410082240cc27905de5c07822500822400822507820800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420800827900824007822505c90907824100822400975c07890904025d0082240b172505c908041725009e2400827902427800827900824009422505c90902424100822400975c07890905de2400824004172505c9780b177905c22400825c04020805d72400827809422505c97807824100822400975c07890907824100822404172505c9780957250082240082790782080,
  0x40094000000000078040000000001e000010000000000000780940000000000cc0780000780000000400017000780000400940000000000000400000000000000780000400000000000b0078000000040000000000000000000000000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e000780000000000000000780000000780000000400000000000000000000000000000010000000000000000940000000780e807800007800000004000170000000004005c0000000000000400000000000000780000400400000000b0000000000040000001e00000078000078000078000040078000000000078040000000000000078000001e0000005c0400000000000b000000000000000005c000000000000000040000000000040000000000000000078000000000000000094000000078094000000000000078000000000078000040094000000000078040000000001e000010000000000000780940000000780e80780000780000000400017000780000400940000000000000400000000000000780000400400000000b0078000000040000001e00000078000078000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e00078000000000000000078000000000000000094000000000000000000000001e000010000000000000000400000000000b007800000000000000000000007800004007800000000007804000000000000007800004005c0000000b0000000000040000001e00000078000078000078000040094000000000000040000000000000078000001e000000400400000000780b00780000000000000400000000000000780940000000780780400000000000000780000780400000000400000000780940000000000000780780000,
  0x2400004009402405c900078040000024001e5c02505c05d72400007809402405c9000cc07800177800005c04000170007800004009402405c90002404000002400175c0789000400240000240b177805c90004002400002400002402400000002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400005de2400005c04172405c97804005c00002405c05c02505c0780400000240cc07805de5c07802400002400002407800000007800002404172405c90002402400002400005c02500005d72400002409402405c9780e807800177800005c04000170002400004005c02405c90002404000002400175c0789000400400000240b172405c900041724001e2400007802407800007800004007802405c90007804000002400175c07890005de2400005c04002405c9000b172400002400005c05c00005c02400002404002405c90004002400002405c05c07895c02402400002409402405c97809402400002400007802570000007800004009572405c900078040000024001e5c02505c05d72400007809402405c9780e807800177800005c04000170007800004009402405c90002404000002400175c0789000400400000240b177805c900041724001e2400007802407800002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400005de2400005c04172405c97804005c00002405c05c02505c0780400000240cc07805de5c07802400002400002407800000002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400000007800004007802405c90007804000002400175c07890004005c0000240b172405c900041724001e2400007802407800007800004009402405c90002404000002400175c07890005de2400004004172405c9780b177805c02400005c04000005d72400007809402405c97807804000002400175c07890007804000002404172405c9780957240000240000780780000,
  0x40094000000000078040000000001e000010000000000000780940000000000cc0780000780000000400017000780000400940000000000000400000000000000780000400000000000b0078000000040000000000000000000000000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e000780000000000000000780000000780000000400000000000000000000000000000010000000000000000940000000780e807800007800000004000170000000004005c0000000000000400000000000000780000400400000000b0000000000040000001e00000078000078000078000040078000000000078040000000000000078000001e0000005c0400000000000b000000000000000005c000000000000000040000000000040000000000000000078000000000000000094000000078094000000000000078000000000078000040094000000000078040000000001e000010000000000000780940000000780e80780000780000000400017000780000400940000000000000400000000000000780000400400000000b0078000000040000001e00000078000078000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e00078000000000000000078000000000000000094000000000000000000000001e000010000000000000000400000000000b007800000000000000000000007800004007800000000007804000000000000007800004005c0000000b0000000000040000001e00000078000078000078000040094000000000000040000000000000078000001e000000400400000000780b00780000000000000400000000000000780940000000780780400000000000000780000780400000000400000000780940000000000000780780000,
  0x822400824009422505c909078241008224009e5c02505c05d72400827809422505c9080cc27900977800825c04020970827900824009422505c90902424100822400975c0789090402250082240b177905c90804022500822400822502420800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420805de2400825c04172505c97804025d00822405c25c02505d0782410082240cc27905de5c07822500822400822507820800827800822404172505c90802422500822400825c02500805d72400822409422505c9780e827900977800825c04020970822500824005c22505c90902424100822400975c0789090402410082240b172505c908041725009e2400827902427800827800824007822505c90907824100822400975c07890905de2400825c04022505c9080b172500822400825c05c20805c22400822404022505c90804022500822405c25c07895d02422500822409422505c97809422500822400827902570800827800824009572505c909078241008224009e5c02505c05d72400827809422505c9780e827900977800825c04020970827900824009422505c90902424100822400975c0789090402410082240b177905c908041725009e2400827902427800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420805de2400825c04172505c97804025d00822405c25c02505d0782410082240cc27905de5c07822500822400822507820800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420800827900824007822505c90907824100822400975c07890904025d0082240b172505c908041725009e2400827902427800827900824009422505c90902424100822400975c07890905de2400824004172505c9780b177905c22400825c04020805d72400827809422505c97807824100822400975c07890907824100822404172505c9780957250082240082790782080,
  0x900040094000900000978040900000001e000010009000009000780940009000009cc0789000780000000400017000789000400940009000009000409000000000000780009400009000000b0078900000940000900000000000900000000000900000094000900000900000900000001e000010009000009000000400009000009b0078900000000000000000001e0090005c04000090007894005c9000000000000010009780409000000cc078901e009780009000000000009780000000789000000400009000009000009000000000000010009000009000000940009000789e807890007800000004000170000090004005c0009000009000409000000000000780009400409000000b0000900000940000901e00000078900078000078900040078000900000978040900000000000078000901e0090005c0400009000009b000090000000000005c000000000900000040000900000940000900000000000078000900000900000094000900078994000900000000078900000000078900040094000900000978040900000001e000010009000009000780940009000789e80789000780000000400017000789000400940009000009000409000000000000780009400409000000b0078900000940000901e00000078900078000000900000094000900000900000900000001e000010009000009000000400009000009b0078900000000000000000001e0090005c04000090007894005c9000000000000010009780409000000cc078901e00978000900000000000978000000000900000094000900000900000900000001e000010009000009000000400009000009b007890000000000000000000007890004007800090000097804090000000000007800094005c9000000b0000900000940000901e00000078900078000078900040094000900000900040900000000000078000901e009000400400009000789b00789000000000000400000000009000780940009000789780409000000000000780009780409000000400009000789940009000000000789780000,
  0x2400004009402405c900078040000024001e5c02505c05d72400007809402405c9000cc07800177800005c04000170007800004009402405c90002404000002400175c0789000400240000240b177805c90004002400002400002402400000002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400005de2400005c04172405c97804005c00002405c05c02505c0780400000240cc07805de5c07802400002400002407800000007800002404172405c90002402400002400005c02500005d72400002409402405c9780e807800177800005c04000170002400004005c02405c90002404000002400175c0789000400400000240b172405c900041724001e2400007802407800007800004007802405c90007804000002400175c07890005de2400005c04002405c9000b172400002400005c05c00005c02400002404002405c90004002400002405c05c07895c02402400002409402405c97809402400002400007802570000007800004009572405c900078040000024001e5c02505c05d72400007809402405c9780e807800177800005c04000170007800004009402405c90002404000002400175c0789000400400000240b177805c900041724001e2400007802407800002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400005de2400005c04172405c97804005c00002405c05c02505c0780400000240cc07805de5c07802400002400002407800000002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400000007800004007802405c90007804000002400175c07890004005c0000240b172405c900041724001e2400007802407800007800004009402405c90002404000002400175c07890005de2400004004172405c9780b177805c02400005c04000005d72400007809402405c97807804000002400175c07890007804000002404172405c9780957240000240000780780000,
  0x40094000000000078040000000001e000010000000000000780940000000000cc0780000780000000400017000780000400940000000000000400000000000000780000400000000000b0078000000040000000000000000000000000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e000780000000000000000780000000780000000400000000000000000000000000000010000000000000000940000000780e807800007800000004000170000000004005c0000000000000400000000000000780000400400000000b0000000000040000001e00000078000078000078000040078000000000078040000000000000078000001e0000005c0400000000000b000000000000000005c000000000000000040000000000040000000000000000078000000000000000094000000078094000000000000078000000000078000040094000000000078040000000001e000010000000000000780940000000780e80780000780000000400017000780000400940000000000000400000000000000780000400400000000b0078000000040000001e00000078000078000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e00078000000000000000078000000000000000094000000000000000000000001e000010000000000000000400000000000b007800000000000000000000007800004007800000000007804000000000000007800004005c0000000b0000000000040000001e00000078000078000078000040094000000000000040000000000000078000001e000000400400000000780b00780000000000000400000000000000780940000000780780400000000000000780000780400000000400000000780940000000000000780780000,
  0x822400824009422505c909078241008224009e5c02505c05d72400827809422505c9080cc27900977800825c04020970827900824009422505c90902424100822400975c0789090402250082240b177905c90804022500822400822502420800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420805de2400825c04172505c97804025d00822405c25c02505d0782410082240cc27905de5c07822500822400822507820800827800822404172505c90802422500822400825c02500805d72400822409422505c9780e827900977800825c04020970822500824005c22505c90902424100822400975c0789090402410082240b172505c908041725009e2400827902427800827800824007822505c90907824100822400975c07890905de2400825c04022505c9080b172500822400825c05c20805c22400822404022505c90804022500822405c25c07895d02422500822409422505c97809422500822400827902570800827800824009572505c909078241008224009e5c02505c05d72400827809422505c9780e827900977800825c04020970827900824009422505c90902424100822400975c0789090402410082240b177905c908041725009e2400827902427800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420805de2400825c04172505c97804025d00822405c25c02505d0782410082240cc27905de5c07822500822400822507820800822500822409422505c90902422500822405de5c02500805c22400822404022505c9080b177905c22400825c02420800827900824007822505c90907824100822400975c07890904025d0082240b172505c908041725009e2400827902427800827900824009422505c90902424100822400975c07890905de2400824004172505c9780b177905c22400825c04020805d72400827809422505c97807824100822400975c07890907824100822404172505c9780957250082240082790782080,
  0x40094000000000078040000000001e000010000000000000780940000000000cc0780000780000000400017000780000400940000000000000400000000000000780000400000000000b0078000000040000000000000000000000000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e000780000000000000000780000000780000000400000000000000000000000000000010000000000000000940000000780e807800007800000004000170000000004005c0000000000000400000000000000780000400400000000b0000000000040000001e00000078000078000078000040078000000000078040000000000000078000001e0000005c0400000000000b000000000000000005c000000000000000040000000000040000000000000000078000000000000000094000000078094000000000000078000000000078000040094000000000078040000000001e000010000000000000780940000000780e80780000780000000400017000780000400940000000000000400000000000000780000400400000000b0078000000040000001e00000078000078000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e00078000000000000000078000000000000000094000000000000000000000001e000010000000000000000400000000000b007800000000000000000000007800004007800000000007804000000000000007800004005c0000000b0000000000040000001e00000078000078000078000040094000000000000040000000000000078000001e000000400400000000780b00780000000000000400000000000000780940000000780780400000000000000780000780400000000400000000780940000000000000780780000,
  0x2400004009402405c900078040000024001e5c02505c05d72400007809402405c9000cc07800177800005c04000170007800004009402405c90002404000002400175c0789000400240000240b177805c90004002400002400002402400000002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400005de2400005c04172405c97804005c00002405c05c02505c0780400000240cc07805de5c07802400002400002407800000007800002404172405c90002402400002400005c02500005d72400002409402405c9780e807800177800005c04000170002400004005c02405c90002404000002400175c0789000400400000240b172405c900041724001e2400007802407800007800004007802405c90007804000002400175c07890005de2400005c04002405c9000b172400002400005c05c00005c02400002404002405c90004002400002405c05c07895c02402400002409402405c97809402400002400007802570000007800004009572405c900078040000024001e5c02505c05d72400007809402405c9780e807800177800005c04000170007800004009402405c90002404000002400175c0789000400400000240b177805c900041724001e2400007802407800002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400005de2400005c04172405c97804005c00002405c05c02505c0780400000240cc07805de5c07802400002400002407800000002400002409402405c90002402400002405de5c02500005c02400002404002405c9000b177805c02400005c02400000007800004007802405c90007804000002400175c07890004005c0000240b172405c900041724001e2400007802407800007800004009402405c90002404000002400175c07890005de2400004004172405c9780b177805c02400005c04000005d72400007809402405c97807804000002400175c07890007804000002404172405c9780957240000240000780780000,
  0x40094000000000078040000000001e000010000000000000780940000000000cc0780000780000000400017000780000400940000000000000400000000000000780000400000000000b0078000000040000000000000000000000000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e000780000000000000000780000000780000000400000000000000000000000000000010000000000000000940000000780e807800007800000004000170000000004005c0000000000000400000000000000780000400400000000b0000000000040000001e00000078000078000078000040078000000000078040000000000000078000001e0000005c0400000000000b000000000000000005c000000000000000040000000000040000000000000000078000000000000000094000000078094000000000000078000000000078000040094000000000078040000000001e000010000000000000780940000000780e80780000780000000400017000780000400940000000000000400000000000000780000400400000000b0078000000040000001e00000078000078000000000000094000000000000000000000001e000010000000000000000400000000000b0078000000000000000000001e0000005c04000000007804005c0000000000000010000780400000000cc078001e00078000000000000000078000000000000000094000000000000000000000001e000010000000000000000400000000000b007800000000000000000000007800004007800000000007804000000000000007800004005c0000000b0000000000040000001e00000078000078000078000040094000000000000040000000000000078000001e000000400400000000780b00780000000000000400000000000000780940000000780780400000000000000780000780400000000400000000780940000000000000780780000
]

/-! ### States, the step and the check -/

/-- The block `0011011`, letter `p` at phase `p`. -/
def w0011011 : List Bool := [false, false, true, true, false, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `6 w .. 6 w + 5` of table
`16 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (16 * p + s) 0 >>> (6 * w)) % 64

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `000`, `00111`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 8 == 0) ||
    ((2 * s + b.toNat) % 32 == 7)

/-- The last 4 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 16 else s

/-- The window of columns 1..10 after a step from phase `p`, with column 11 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 10 (w0011011.getD p false) z w

/-- The certificate at one state: ranks are at most 59; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 7) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 7) (sNext p s w) (wNext p w true)
  decide (r ≤ 59) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 1024

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 16 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 16 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 16 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 16 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 16 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 16 = true := by decide +kernel
theorem ok_6 : allBelowT (partOK 6) 16 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 7 → allBelowT (partOK p) 16 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | 6, _ => ok_6
  | p + 7, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 7) (hs : s < 16) (hw : w < 2 ^ 10) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 10 = 1024 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 59 ∧
      (rk p s w = 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `0011011` read from phase `ph`: letter `(t + ph) % 7` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w0011011.getD ((t + ph) % 7) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..10` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 10
  | t + 1 => stripStep 10 (F t 0) (F t 11) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 10 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 10).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last four readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 7) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 16
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 16
    unfold sNext
    cases ((t + ph) % 7 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 16

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 7) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 11) := by
  show stripStep 10 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `59 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 59 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 11)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 7 = ((t + ph) % 7 + 1) % 7 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 59 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 59 ≤ t) (hp : (t + ph) % 7 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 7 = 0) :
    suf ph (drv (ctr ph) R) (t + 7) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 7) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  have h7 : suf ph (drv (ctr ph) R) (t + 7) = suf ph (drv (ctr ph) R) (t + 6) := by
    show sNext ((t + 6 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 6)) (win (drv (ctr ph) R) (t + 6)) = _
    exact sNext_ne (by omega)
  rw [h7, h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_000 : ∀ s, s < 16 → badB (push (push s false) false) false = true := by decide +kernel
theorem bad_00111 : ∀ s, s < 16 → badB (push (push (push (push s false) false) true) true) true = true
    := by decide +kernel

end ReadingWords.B0011011

open ReadingWords.B0011011

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `000`.** At the first white steps, column 1 never reads `000` with the first reading at time `45` or
later. -/
theorem no_000_time_0011011 (u : Nat) (hu : 45 ≤ u) (hp : (u + ph) % 7 = 0) :
    ¬ (drv (ctr ph) R u 1 = false ∧ drv (ctr ph) R (u + 7) 1 = false ∧ drv (ctr ph) R (u + 14) 1 = false) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 14 = u + 7 + 7 by omega] at h2
  have hb := no_bad R ph (u + 7 + 7) (by omega) (by omega)
  rw [suf_period R ph (u + 7) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_000 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `00111`.** At the first white steps, column 1 never reads `00111` with the first reading at time `31` or
later. -/
theorem no_00111_time_0011011 (u : Nat) (hu : 31 ≤ u) (hp : (u + ph) % 7 = 0) :
    ¬ (drv (ctr ph) R u 1 = false ∧ drv (ctr ph) R (u + 7) 1 = false ∧ drv (ctr ph) R (u + 14) 1 = true ∧
      drv (ctr ph) R (u + 21) 1 = true ∧ drv (ctr ph) R (u + 28) 1 = true) := by
  rintro ⟨h0, h1, h2, h3, h4⟩
  rw [show u + 14 = u + 7 + 7 by omega] at h2
  rw [show u + 21 = u + 7 + 7 + 7 by omega] at h3
  rw [show u + 28 = u + 7 + 7 + 7 + 7 by omega] at h4
  have hb := no_bad R ph (u + 7 + 7 + 7 + 7) (by omega) (by omega)
  rw [suf_period R ph (u + 7 + 7 + 7) (by omega), suf_period R ph (u + 7 + 7) (by omega),
    suf_period R ph (u + 7) (by omega), suf_period R ph u hp, h0, h1, h2, h3, h4] at hb
  rw [bad_00111 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B0011011

/-- A sequence of bits has none of the factors `000`, `00111` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = false ∧ b (i + 1) = false ∧ b (i + 2) = false) ∧
    ¬ (b i = false ∧ b (i + 1) = false ∧ b (i + 2) = true ∧ b (i + 3) = true ∧ b (i + 4) = true)

/-- Column 1 of the right half driven by `0011011` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 7 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (7 * i + (7 - ph % 7) % 7) 1

end ReadingWords.B0011011

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`000`, `00111` from the 7th on. -/
theorem readings_0011011 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 7 := by
  intro i hi
  have hp : (7 * i + (7 - ph % 7) % 7 + ph) % 7 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 7) 1 := by
    unfold reading; rw [show 7 * (i + 1) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 7 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 14) 1 := by
    unfold reading; rw [show 7 * (i + 2) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 14 by omega]
  have e3 : reading R ph (i + 3) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 21) 1 := by
    unfold reading; rw [show 7 * (i + 3) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 21 by omega]
  have e4 : reading R ph (i + 4) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 28) 1 := by
    unfold reading; rw [show 7 * (i + 4) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 28 by omega]
  rw [e1, e2, e3, e4]
  exact ⟨no_000_time_0011011 R ph _ (by omega) hp, no_00111_time_0011011 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `0011011` -/

namespace ReadingWords.B0011011

/-- From time `T` on, a row whose center column repeats `0011011` from `T` has the right half driven by `0011011` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0011011.getD ((t - T) % 7) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w0011011.getD ((0 + 0) % 7) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w0011011.getD ((t + 1 + 0) % 7) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B0011011

/-- **Readings of every row.** If the center column of a row repeats `0011011` from time `T` (letter
`(t - T) % 7` at time `t`), then column 1 at the times `T + 7 i` avoids `000`, `00111` from `i = 7` on. -/
theorem readings_0011011_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0011011.getD ((t - T) % 7) false) :
    Avoids (fun i => evolve init (T + 7 * i) 1) 7 := by
  have e : (fun i => evolve init (T + 7 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 7 * i = T + (7 * i + (7 - 0 % 7) % 7) by omega]
    exact evolve_eq_drv init T h (7 * i + (7 - 0 % 7) % 7) 1
  rw [e]
  exact readings_0011011 _ 0

end B0011011

/-! ## Block `0110111` -/

section B0110111

/-! The certificate and the helpers live in `ReadingWords.B0110111`; the headline theorems are in `Rule30Open`. -/

namespace ReadingWords.B0110111

/-! ### The certificate: the attractor ranks of the greatest closed good set, rank 0 for the set itself -/

/-- Rank tables: entry `4 * p + s` packs the rank of window `w` in bits `6 w .. 6 w + 5`. -/
def rankTabs : List Nat := [
  0x3c00000000000000000000000003c000000000000000000000000000001d0000000000000000000000000000000000003c00000000000000000000000000000000000000000000003c00000000003c00000000000000000000000160000000003c000000000000000000000001d3c00000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000000007400000000000000000000000000000000000000000000003c00000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000003c00000000003c00000000000000000000000000000000003c000000000000001d0000000003c00000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c00000000000000000000000003c000000000000000000000000000001d0000000000000000000000000000000000003c00000000000000000000000000000000000000000000003c00000000003c00000000000000000000000160000000003c000000000000000000000001d3c00000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000000007400000000000000000000000000000000000160000000003c000000000000000000000001d3c00000000000000000000000000000000000000000000000000000000000000000003c000000000000001d0000000000000000000000000000003c00000000003c00000000000000000000000000000000003c00000000000000000000000003c00000000000000000000000000000000000000000000003c000000000000000000000000000000000001d000000000000000000000000000000000000000000000000000000000,
  0x400400400480400400403c00400400400480400400400403c004004004804004004004004004005d0480400400400400400400400480400400403c00400400400480400400400400400400400480400400403c00400400403c80400400400400400400400560400400403c004004004004804004004005d3c00400400480400400400400400400400480400400400403c00400400480400400400400400400400480400400400400400400400480400400407400400400400480400400400400400400400480400400403c00400400400480400400400403c00400400480400400400400400400400480400400400400400400400480400400403c00400400400480400400400400400400400480400400403c00400400403c80400400400400400400400480400400403c004004004004805d0400400403c00400400480400400400400400400400480400400400403c00400400480400400400400400400400480400400400400400400400480400400400400400400400480400400400400400400400480400400403c00400400400480400400400403c004004004804004004004004004005d0480400400400400400400400480400400403c00400400400480400400400400400400400480400400403c00400400403c80400400400400400400400560400400403c004004004004804004004005d3c00400400480400400400400400400400480400400400403c00400400480400400400400400400400480400400400400400400400480400400407400400400400480400400400400400400400560400400403c004004004004804004004005d3c00400400480400400400400400400400480400400400400400400400480400400403c004004004004805d0400400400400400400480400400403c00400400403c80400400400400400400400480400400403c00400400400480400400400403c00400400480400400400400400400400480400400400403c004004004804004004004004004004004805d040040040040040040048040040040040040040040048040040040040,
  0x400400400400400400403c00400400400400400400400403c004004004004004004004004004005d0400400400400400400400400400400400403c00400400400400400400400400400400400400400400403c00400400403c00400400400400400400400560400400403c004004004004004004004005d3c00400400400400400400400400400400400400400400403c00400400400400400400400400400400400400400400400400400400400400400407400400400400400400400400400400400400400400400403c00400400400400400400400403c00400400400400400400400400400400400400400400400400400400400400400403c00400400400400400400400400400400400400400400403c00400400403c00400400400400400400400400400400403c004004004004005d0400400403c00400400400400400400400400400400400400400400403c00400400400400400400400400400400400400400400400400400400400400400400400400400400400400400400400400400400400400400403c00400400400400400400400403c004004004004004004004004004005d0400400400400400400400400400400400403c00400400400400400400400400400400400400400400403c00400400403c00400400400400400400400560400400403c004004004004004004004005d3c00400400400400400400400400400400400400400400403c00400400400400400400400400400400400400400400400400400400400400400407400400400400400400400400400400400400560400400403c004004004004004004004005d3c00400400400400400400400400400400400400400400400400400400400400400403c004004004004005d0400400400400400400400400400403c00400400403c00400400400400400400400400400400403c00400400400400400400400403c00400400400400400400400400400400400400400400403c004004004004004004004004004004004005d040040040040040040040040040040040040040040040040040040040,
  0x400400400480400400403c00400400400480400400400403c004004004804004004004004004005d0480400400400400400400400480400400403c00400400400480400400400400400400400480400400403c00400400403c80400400400400400400400560400400403c004004004004804004004005d3c00400400480400400400400400400400480400400400403c00400400480400400400400400400400480400400400400400400400480400400407400400400400480400400400400400400400480400400403c00400400400480400400400403c00400400480400400400400400400400480400400400400400400400480400400403c00400400400480400400400400400400400480400400403c00400400403c80400400400400400400400480400400403c004004004004805d0400400403c00400400480400400400400400400400480400400400403c00400400480400400400400400400400480400400400400400400400480400400400400400400400480400400400400400400400480400400403c00400400400480400400400403c004004004804004004004004004005d0480400400400400400400400480400400403c00400400400480400400400400400400400480400400403c00400400403c80400400400400400400400560400400403c004004004004804004004005d3c00400400480400400400400400400400480400400400403c00400400480400400400400400400400480400400400400400400400480400400407400400400400480400400400400400400400560400400403c004004004004804004004005d3c00400400480400400400400400400400480400400400400400400400480400400403c004004004004805d0400400400400400400480400400403c00400400403c80400400400400400400400480400400403c00400400400480400400400403c00400400480400400400400400400400480400400400403c004004004804004004004004004004004805d040040040040040040048040040040040040040040048040040040040,
  0x2300000000000000000000000000000000000000000000000000000000000070000000001500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00000000000000002300000000000000000000000000000000001500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002300000000000000000000000000000000000000000000000000000000000070000000001500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00000000000000002300000000000000000000000000000000001500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001500000000000000000000000000000000000000000000000000000000000000000000000000000000000070000000001500000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c000000000000000000000000,
  0x738000000000700000000e00738000000002300000038000700000000000700000e00000700000038000000038000000770000000001500000000e00738000000000000000000e00738000000000700000e00000700000000000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038038000700000000000700001c00e00738000000002300000000e00738000000000700000e00001538000038000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038000000738000000001500000000e00738000000000000000000e00738000000000700000e00000700000000000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038038000700000000000700000e00e00738000000000000000000e00738000000000700000e00000738000038000700000000000738000000000700000000e00738000000002300000038000700000000000700000e00000700000038000000038000000770000000001500000000e00738000000000000000000e00738000000000700000e00000700000000000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038038000700000000000700001c00e00738000000002300000000e00738000000000700000e00001538000038000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038000000738000000001500000000e00738000000000000000000e00738000000000700000e00000700000000000700000000000770000000001500000000e00738000000000000000038000700000000000700001c00000700000038000000038038000700000000000700000e00e00738000000000000000000e00738000000000700001c000007380000380007000000,
  0x700000000000700000000000700000000002300000000000700000000000700000000000700000000000000000000000770000000001500000000000700000000000000000000000700000000000700000000000700000000000700000000000700000000000700000000000700000000000000000000000700000000000700000000000700000000000000000000000700000000000700001c00000700000000002300000000000700000000000700000000001500000000000700000000000700000000000700000000000700000000000000000000000700000000000700000000000700000000000000000000000700000000001500000000000700000000000000000000000700000000000700000000000700000000000700000000000700000000000700000000000700000000000000000000000700000000000700000000000700000000000000000000000700000000000700000000000700000000000000000000000700000000000700000000000700000000000700000000000700000000000700000000000700000000002300000000000700000000000700000000000700000000000000000000000770000000001500000000000700000000000000000000000700000000000700000000000700000000000700000000000700000000000700000000000700000000000000000000000700000000000700000000000700000000000000000000000700000000000700001c00000700000000002300000000000700000000000700000000001500000000000700000000000700000000000700000000000700000000000000000000000700000000000700000000000700000000000000000000000700000000001500000000000700000000000000000000000700000000000700000000000700000000000700000000000770000000001500000000000700000000000000000000000700000000000700001c00000700000000000000000000000700000000000700000000000700000000000000000000000700000000000700001c000007000000000007000000,
  0x738000000000700000000e00738000000002300000038000700000000000700000e00000700000038000000038000000770000000001500000000e00738000000000000000000e00738000000000700000e00000700000000000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038038000700000000000700001c00e00738000000002300000000e00738000000000700000e00001538000038000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038000000738000000001500000000e00738000000000000000000e00738000000000700000e00000700000000000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038038000700000000000700000e00e00738000000000000000000e00738000000000700000e00000738000038000700000000000738000000000700000000e00738000000002300000038000700000000000700000e00000700000038000000038000000770000000001500000000e00738000000000000000000e00738000000000700000e00000700000000000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038038000700000000000700001c00e00738000000002300000000e00738000000000700000e00001538000038000700000000000738000000000700000000e00738000000000000000038000700000000000700000e00000700000038000000038000000738000000001500000000e00738000000000000000000e00738000000000700000e00000700000000000700000000000770000000001500000000e00738000000000000000038000700000000000700001c00000700000038000000038038000700000000000700000e00e00738000000000000000000e00738000000000700001c000007380000380007000000,
  0x8800000000000000000000000000000000000000000000008800000006c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008800000000000000000000000000000000000000000000008800000006c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050000000000000000000001b0000000000000000000000000000000000000000000000000000000000000000000000000000000000005000000000000000000000008800000006c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x18034018000000000000000018000d18000000d00000000018034018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d18000000000018000018000d18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d18000000000018000018000d18000000000088000018034018000000000000000018000d18000000d0008800001806c018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d50000000000018000018000d18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000050000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d18000000000018000018000d18000000000088000018034018000000000000000018000d18000000d0008800001806c018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d50000000000018000018000d18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d18000000000018000018000d18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d50000000000018000018001b18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000050000018000018000000000d8800001806c018000000000000000018000d18000000d00000000018000d18000000000018000018000d180000000000,
  0x1800001800000000000000001800001800000000000000001800001800000000001800001800001800000000000000001800001800000000000000001800001800000000000000001800001800000000001800001800001800000000000000001800001800000000000000001800001800000000000000001800001800000000001800001800001800000000000000001800001800000000000000001800001800000000000000001800001800000000001800001800001800000000008800001800001800000000000000001800001800000000008800001806c01800000000001800001800001800000000000000001800001800000000000000001800001800000000000000001800005000000000001800001800001800000000000000001800001800000000000000001800001800000000000000001800001800000000005000001800001800000000000000001800001800000000000000001800001800000000000000001800001800000000001800001800001800000000008800001800001800000000000000001800001800000000008800001806c018000000000018000018000018000000000000000018000018000000000000000018000018000000000000000018000050000000000018000018000018000000000000000018000018000000000000000018000018000000000000000018000018000000000018000018000018000000000000000018000018000000000000000018000018000000000000000018000018000000000018000018000018000000000000000018000018000000000000000018000018000000000000000018000018000000000018000018000018000000000000000018000018000000000000000018000018000000000000000018000050000000000018000018001b1800000000000000001800001800000000000000001800001800000000000000001800001800000000005000001800001800000000008800001806c0180000000000000000180000180000000000000000180000180000000000180000180000180000000000,
  0x18034018000000000000000018000d18000000d00000000018034018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d18000000000018000018000d18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d18000000000018000018000d18000000000088000018034018000000000000000018000d18000000d0008800001806c018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d50000000000018000018000d18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000050000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d18000000000018000018000d18000000000088000018034018000000000000000018000d18000000d0008800001806c018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d50000000000018000018000d18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d18000000000018000018000d18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000018000018000018000000000d00000018034018000000000000000018000d18000000d00000000018000d50000000000018000018001b18000000000000000018034018000000000000000018000d18000000d00000000018034018000000000050000018000018000000000d8800001806c018000000000000000018000d18000000d00000000018000d18000000000018000018000d180000000000,
  0x1300000000000000000000000000068000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068000000000000000000000000000000000000000000000000000000000000000000000001300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00000000000000000002100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002100000000000000000000001300000000000000000000000000068000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x500c00000001300030000000500000000030000068000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000030000000500c00000000500030000000500000000068000030000000500c00000000500c00000000500000000000000000000000500c00000001300030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000501a00000000500000030002100030000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000000002100000000000500c00000001300030000000500000000030000068000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000030000000500c00000000500030000000500000000068000030000000500c00000000500c00000000500000000000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000501a00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000068000000500c00000000500030000000500000000030000030000000500c00000000500c000000005000000000000,
  0x500000000001300000000000500000000000000068000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000068000000000000500000000000500000000000500000000000000000000000500000000001300000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000501a00000000500000000002100000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000002100000000000500000000001300000000000500000000000000068000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000068000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000500000000000500000000000500000000000000000000000501a000000005000000000005000000000000000000000005000000000005000000000005000000000000000000000005000000000005000000000005000000000000000680000005000000000005000000000005000000000000000000000005000000000005000000000005000000000000,
  0x500c00000001300030000000500000000030000068000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000030000000500c00000000500030000000500000000068000030000000500c00000000500c00000000500000000000000000000000500c00000001300030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000501a00000000500000030002100030000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000000002100000000000500c00000001300030000000500000000030000068000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000030000000500c00000000500030000000500000000068000030000000500c00000000500c00000000500000000000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000501a00000000500c00000000500000030000000000000000500c00000000500030000000500000000030000030000000500c00000000500c00000000500000030000000068000000500c00000000500030000000500000000030000030000000500c00000000500c000000005000000000000,
  0x640000000000000000000000000020000000000000000000020000000000000000000012000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000000000000000000000000000000000000000000000012020000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000020000000000000000000000000000000000012000000000000000000000000000000000000000000000000000012000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000000000000000000000000000000000000000000000000000000000012000000020000000000000000000000000000000000000000000000640000000000000012000000000020000000000000000000020000000000000000000012000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000000000000000000000000000000000000000000000012020000000000000000000000000000000000000000000000000000000000000000000000000000000000000012000000000020000000000000000000000000000000000012000000000000000000000000000000000000000000000000000012020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000652020000000000000000000000020000000000000000000000000000000000000012000000000000000000000000000000000000,
  0x40000040000046400000000040000040002c40000200000040000040000042e00000000040000040002d20000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040000040000000000040000040000042c00000000040000120002c40000000000040000040000042c00000000040000040002d20200000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000120000040000200000040000040000042c00000000040000120002c40000000000040000040000042c00000000040000040002d20000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040000040000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040002d20000000000040000040000042c00000000040000040002c40000000000040000120000042e00000000040000040000040000000000040000040000046400000000040000120002c40000200000040000040000042e00000000040000040002d20000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040000040000000000040000040000042c00000000040000120002c40000000000040000040000042c00000000040000040002d20200000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000120000040000200000040000040000042c00000000040000120002c40000000000040000040000042c00000000040000040002d20200000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040000040000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040006520200000000040000040000042e00000000040000040002c40000000000040000120000042c0000000004000004000004000000,
  0x4000004000004640000000004000004000004000020000004000004000004020000000004000004000012000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000012000004000000000004000004000004000000000004000004000012020000000004000004000004000000000004000004000004000000000004000004000004000000000004000012000004000020000004000004000004000000000004000012000004000000000004000004000004000000000004000004000012000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000012000000000004000004000004000000000004000004000004000000000004000012000004020000000004000004000004000000000004000004000004640000000004000012000004000020000004000004000004020000000004000004000012000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000012000004000000000004000004000004000000000004000004000012020000000004000004000004000000000004000004000004000000000004000004000004000000000004000012000004000020000004000004000004000000000004000012000004000000000004000004000004000000000004000004000012020000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000004000000000004000004000652020000000004000004000004020000000004000004000004000000000004000012000004000000000004000004000004000000,
  0x40000040000046400000000040000040002c40000200000040000040000042e00000000040000040002d20000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040000040000000000040000040000042c00000000040000120002c40000000000040000040000042c00000000040000040002d20200000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000120000040000200000040000040000042c00000000040000120002c40000000000040000040000042c00000000040000040002d20000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040000040000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040002d20000000000040000040000042c00000000040000040002c40000000000040000120000042e00000000040000040000040000000000040000040000046400000000040000120002c40000200000040000040000042e00000000040000040002d20000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040000040000000000040000040000042c00000000040000120002c40000000000040000040000042c00000000040000040002d20200000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000120000040000200000040000040000042c00000000040000120002c40000000000040000040000042c00000000040000040002d20200000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040000040000000000040000040000042c00000000040000040002c40000000000040000040000042c00000000040000040006520200000000040000040000042e00000000040000040002c40000000000040000120000042c0000000004000004000004000000,
  0x44000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044000000000000000000000000044000000000000000000000000000000000000000000000000000000000000000000044000000000001f00000000000000000000000000000000000000000000000000044000001f0000000000000000000000004400000000000000000004400000000000000000000000000000000000000000000000000000000000000000000004400180000000000000000000000000000000000000007c00000000000000000000000000000000000000000000000004400000000000000000000000004400000000000000000000000000000000000000007c00000000000000000000000004400000000000000000000000000000000000000000000000000000000000000004400000000000000000000000000000004400000000000000000004400000000000000000007c00000000000000000000000000000000000000000000000004400180000000000000000000000000000000000000007c00000000000000000000000000000000000000000000000004400000000000000000000000004400000000000000000000000000000000000000007c000000000000000000000000044000000000001f00000000000000000000000000000000000000000000000000044000001f00000000000000000000000044000000000000000000044000000000000000000000000000000000000000000000000000000000000000000000044000000000001f0000000000000000000000000000000000000000000000000004400000000000000000000000000004400000000000000000000000004400000000000000000000000000000000000000007c000000000000000000000000044000000000000000000000001f0000000000000000000000000000000000000004400000000000000000000000007c0440000000000000000000000440018000000000000000000000000000000000000000000,
  0xc00ca0c00000c00c00c00004400ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c044a0c00000c00c00c00000c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000df0c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c04400000df0ca0c00000c00c00c00000c044a0c00000c00c00c00004400ca0c00000c00c00c00000c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400d80c00000c00c00c00000c00ca0c00000c00c00c07c00c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c044a0c00000c00c00c00000c00c00c00000c00c00c07c00c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c04400000c00ca0c00000c00c00c00000c044a0c00000c00c00c00004400ca0c00000c00c00c07c00c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400d80c00000c00c00c00000c00ca0c00000c00c00c07c00c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c044a0c00000c00c00c00000c00c00c00000c00c00c07c00c00ca0c00000c00c00c00004400ca0c00000df0c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c04400000df0ca0c00000c00c00c00000c044a0c00000c00c00c00004400ca0c00000c00c00c00000c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000df0c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c04400000c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c044a0c00000c00c00c00000c00c00c00000c00c00c07c00c00ca0c00000c00c00c00004400ca0c00000c00c00c00000df0ca0c00000c00c00c00000c00c00c00000c00c04400000c00ca0c00000c00c00c07c04400ca0c00000c00c00c00004400d80c00000c00c00c00000c00c00c00000c00c00c0000,
  0xc00c00c00000c00c00c00004400c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00004400c00c00000c00c00c00000c04400c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00004400c00c00000df0c00c00000c00c00c00000c00c00c00000c00c00c00000c00c04400000df0c00c00000c00c00c00000c04400c00000c00c00c00004400c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00004400d80c00000c00c00c00000c00c00c00000c00c00c07c00c00c00c00000c00c00c00000c00c00c00000c00c00c00004400c00c00000c00c00c00000c04400c00000c00c00c00000c00c00c00000c00c00c07c00c00c00c00000c00c00c00004400c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c04400000c00c00c00000c00c00c00000c04400c00000c00c00c00004400c00c00000c00c00c07c00c00c00c00000c00c00c00000c00c00c00000c00c00c00004400d80c00000c00c00c00000c00c00c00000c00c00c07c00c00c00c00000c00c00c00000c00c00c00000c00c00c00004400c00c00000c00c00c00000c04400c00000c00c00c00000c00c00c00000c00c00c07c00c00c00c00000c00c00c00004400c00c00000df0c00c00000c00c00c00000c00c00c00000c00c00c00000c00c04400000df0c00c00000c00c00c00000c04400c00000c00c00c00004400c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00000c00c00c00004400c00c00000df0c00c00000c00c00c00000c00c00c00000c00c00c00000c00c04400000c00c00c00000c00c00c00004400c00c00000c00c00c00000c04400c00000c00c00c00000c00c00c00000c00c00c07c00c00c00c00000c00c00c00004400c00c00000c00c00c00000df0c00c00000c00c00c00000c00c00c00000c00c04400000c00c00c00000c00c00c07c04400c00c00000c00c00c00004400d80c00000c00c00c00000c00c00c00000c00c00c0000,
  0xc00ca0c00000c00c00c00004400ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c044a0c00000c00c00c00000c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000df0c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c04400000df0ca0c00000c00c00c00000c044a0c00000c00c00c00004400ca0c00000c00c00c00000c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400d80c00000c00c00c00000c00ca0c00000c00c00c07c00c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c044a0c00000c00c00c00000c00c00c00000c00c00c07c00c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c04400000c00ca0c00000c00c00c00000c044a0c00000c00c00c00004400ca0c00000c00c00c07c00c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400d80c00000c00c00c00000c00ca0c00000c00c00c07c00c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c044a0c00000c00c00c00000c00c00c00000c00c00c07c00c00ca0c00000c00c00c00004400ca0c00000df0c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c04400000df0ca0c00000c00c00c00000c044a0c00000c00c00c00004400ca0c00000c00c00c00000c00c00c00000c00c00c00000c00ca0c00000c00c00c00004400ca0c00000df0c00c00000c00ca0c00000c00c00c00000c00c00c00000c00c04400000c00ca0c00000c00c00c00004400ca0c00000c00c00c00000c044a0c00000c00c00c00000c00c00c00000c00c00c07c00c00ca0c00000c00c00c00004400ca0c00000c00c00c00000df0ca0c00000c00c00c00000c00c00c00000c00c04400000c00ca0c00000c00c00c07c04400ca0c00000c00c00c00004400d80c00000c00c00c00000c00c00c00000c00c00c0000,
  0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000107800000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000005c000000000000000000000001e00000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000001e0000000000000000000000000000000000000000000000000000000000000007800000000005c000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000107800000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000005c000000000000000000000001e0000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000005c000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000100000000000000000000000000000005c0000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000,
  0x22400020000020000020000022400022400100000020000022400020000020000020000022400022400020000020000022400020000020000020000022400022400020000107800022400020000020000020000022400022400020000020000022400020000020000020000022400022400100000020000022400020000020000020000025c000224000200000200000225e00200000200000200000224000224000200001000000224000200000200000200000224000224000200000200000224000200000200000200000224000224001000000200000224000200000200000200000224000224000201e00200000224000200000200000200000224000224000200001000000224000200000200000200000224000224000200000200000224000200000200000200000224000224000200001000000225e0020000020000020000022400022400020000020000022400020000020000027800022400025c000200001000000224000200000200000200000224000224000200000200000224000200000200000200000224000224001000000200000224000200000200000200000224000224000201e0020000022400020000020000020000022400022400020000107800022400020000020000020000022400022400020000020000022400020000020000020000022400022400100000020000022400020000020000020000025c000224000200000200000225e0020000020000020000022400022400020000100000022400020000020000020000022400022400020000020000022400020000020000020000022400022400100000020000022400020000020000020000025c000224000200000200000224000200000200000200000224000224000200001000000224000200000200000200000224000225e0020000020000022400020000020000020000022400022400020000100000022400020000020000020000025c0002240002000002000002240002000002000002000002240002240002000010000002240002000002000002000002240002240002000002,
  0x20000020000020000020000020000020000100000020000020000020000020000020000020000020000020000020000020000020000020000020000020000020000020000107800020000020000020000020000020000020000020000020000020000020000020000020000020000020000100000020000020000020000020000020000025c000200000200000200000201e00200000200000200000200000200000200001000000200000200000200000200000200000200000200000200000200000200000200000200000200000200001000000200000200000200000200000200000200000200000201e00200000200000200000200000200000200000200000200001000000200000200000200000200000200000200000200000200000200000200000200000200000200000200000200001000000201e0020000020000020000020000020000020000020000020000020000020000027800020000025c000200001000000200000200000200000200000200000200000200000200000200000200000200000200000200000200001000000200000200000200000200000200000200000200000201e0020000020000020000020000020000020000020000020000107800020000020000020000020000020000020000020000020000020000020000020000020000020000020000100000020000020000020000020000020000025c000200000200000200000201e0020000020000020000020000020000020000100000020000020000020000020000020000020000020000020000020000020000020000020000020000020000100000020000020000020000020000020000025c000200000200000200000200000200000200000200000200000200000200001000000200000200000200000200000200000201e0020000020000020000020000020000020000020000020000020000100000020000020000020000020000025c0002000002000002000002000002000002000002000002000002000002000010000002000002000002000002000002000002000002000002,
  0x22400020000020000020000022400022400100000020000022400020000020000020000022400022400020000020000022400020000020000020000022400022400020000107800022400020000020000020000022400022400020000020000022400020000020000020000022400022400100000020000022400020000020000020000025c000224000200000200000225e00200000200000200000224000224000200001000000224000200000200000200000224000224000200000200000224000200000200000200000224000224001000000200000224000200000200000200000224000224000201e00200000224000200000200000200000224000224000200001000000224000200000200000200000224000224000200000200000224000200000200000200000224000224000200001000000225e0020000020000020000022400022400020000020000022400020000020000027800022400025c000200001000000224000200000200000200000224000224000200000200000224000200000200000200000224000224001000000200000224000200000200000200000224000224000201e0020000022400020000020000020000022400022400020000107800022400020000020000020000022400022400020000020000022400020000020000020000022400022400100000020000022400020000020000020000025c000224000200000200000225e0020000020000020000022400022400020000100000022400020000020000020000022400022400020000020000022400020000020000020000022400022400100000020000022400020000020000020000025c000224000200000200000224000200000200000200000224000224000200001000000224000200000200000200000224000225e0020000020000022400020000020000020000022400022400020000100000022400020000020000020000025c0002240002000002000002240002000002000002000002240002240002000010000002240002000002000002000002240002240002000002
]

/-! ### States, the step and the check -/

/-- The block `0110111`, letter `p` at phase `p`. -/
def w0110111 : List Bool := [false, true, true, false, true, true, true]

/-- The rank of the state with phase `p`, last readings `s` and window `w`: bits `6 w .. 6 w + 5` of table
`4 p + s`. -/
def rk (p s w : Nat) : Nat := (rankTabs.getD (4 * p + s) 0 >>> (6 * w)) % 64

/-- The reading `b` after the readings `s` (newest in bit 0) completes one of `11`, `101`. -/
def badB (s : Nat) (b : Bool) : Bool :=
  ((2 * s + b.toNat) % 4 == 3) ||
    ((2 * s + b.toNat) % 8 == 5)

/-- The last 2 readings after a step from phase `p` with window `w`: at phase 0 column 1 is read. -/
def sNext (p s w : Nat) : Nat := bif p == 0 then (2 * s + (w.testBit 0).toNat) % 4 else s

/-- The window of columns 1..10 after a step from phase `p`, with column 11 equal to `z`. -/
def wNext (p w : Nat) (z : Bool) : Nat := stripStep 10 (w0110111.getD p false) z w

/-- The certificate at one state: ranks are at most 35; a state of rank 0 goes to states of rank 0 and completes no
forbidden word; a state of positive rank goes to states of smaller rank. -/
def nodeOK (p s w : Nat) : Bool :=
  let r := rk p s w
  let r0 := rk ((p + 1) % 7) (sNext p s w) (wNext p w false)
  let r1 := rk ((p + 1) % 7) (sNext p s w) (wNext p w true)
  decide (r ≤ 35) && (r != 0 || (r0 == 0 && r1 == 0 && !(p == 0 && badB s (w.testBit 0)))) &&
    (r == 0 || (decide (r0 < r) && decide (r1 < r)))

/-- The certificate at every window, for the phase `p` and the readings `s`. -/
def partOK (p s : Nat) : Bool := allBelowT (fun w => nodeOK p s w) 1024

/-! ### The kernel checks, one per phase -/

theorem ok_0 : allBelowT (partOK 0) 4 = true := by decide +kernel
theorem ok_1 : allBelowT (partOK 1) 4 = true := by decide +kernel
theorem ok_2 : allBelowT (partOK 2) 4 = true := by decide +kernel
theorem ok_3 : allBelowT (partOK 3) 4 = true := by decide +kernel
theorem ok_4 : allBelowT (partOK 4) 4 = true := by decide +kernel
theorem ok_5 : allBelowT (partOK 5) 4 = true := by decide +kernel
theorem ok_6 : allBelowT (partOK 6) 4 = true := by decide +kernel

theorem parts_ok : ∀ p, p < 7 → allBelowT (partOK p) 4 = true
  | 0, _ => ok_0
  | 1, _ => ok_1
  | 2, _ => ok_2
  | 3, _ => ok_3
  | 4, _ => ok_4
  | 5, _ => ok_5
  | 6, _ => ok_6
  | p + 7, h => absurd h (by omega)

theorem node_ok {p s w : Nat} (hp : p < 7) (hs : s < 4) (hw : w < 2 ^ 10) : nodeOK p s w = true :=
  allBelowT_spec (allBelowT_spec (parts_ok p hp) s hs) w (by have : (2 : Nat) ^ 10 = 1024 := rfl; omega)

theorem node_facts {p s w : Nat} (h : nodeOK p s w = true) (z : Bool) :
    rk p s w ≤ 35 ∧
      (rk p s w = 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) = 0 ∧
        (p = 0 → badB s (w.testBit 0) = false)) ∧
      (rk p s w ≠ 0 → rk ((p + 1) % 7) (sNext p s w) (wNext p w z) < rk p s w) := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hM, hA⟩, hB⟩ := h
  refine ⟨hM, fun h0 => ?_, fun h0 => ?_⟩
  · rcases hA with hA | ⟨⟨r0, r1⟩, hbad⟩
    · exact absurd h0 hA
    · refine ⟨by cases z <;> assumption, fun hp => ?_⟩
      subst hp
      simpa using hbad
  · rcases hB with hB | ⟨r0, r1⟩
    · exact absurd hB h0
    · cases z <;> assumption

/-! ### The driven right half and its states -/

/-- The center column `0110111` read from phase `ph`: letter `(t + ph) % 7` of the block at step `t`. -/
def ctr (ph t : Nat) : Bool := w0110111.getD ((t + ph) % 7) false

/-- The first `n` values of `f` as bits. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => pack f n ||| ((f n).toNat <<< n)

theorem testBit_pack (f : Nat → Bool) : ∀ n i, (pack f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [pack]
  | n + 1, i => by
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_toNat, testBit_pack f n i]
    rcases Nat.lt_trichotomy i n with h | h | h
    · simp [h, show ¬ n ≤ i by omega, show i < n + 1 by omega]
    · subst h; simp
    · simp [show ¬ i < n by omega, show i - n ≠ 0 by omega, show ¬ i < n + 1 by omega]

theorem pack_lt (f : Nat → Bool) (n : Nat) : pack f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_pack, decide_eq_false (by omega), Bool.false_and]

/-- The windows of columns `1..10` of `F`, step by step. -/
def win (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => pack (fun i => F 0 (i + 1)) 10
  | t + 1 => stripStep 10 (F t 0) (F t 11) (win F t)

theorem win_enc {F : Nat → Nat → Bool} (hF : IsR30 F) : ∀ t, EncF F 10 t 0 (win F t)
  | 0 => ⟨pack_lt _ _, fun i hi => by
      show (pack (fun i => F 0 (i + 1)) 10).testBit i = F 0 (0 + 1 + i)
      rw [testBit_pack, decide_eq_true hi, Bool.true_and, show 0 + 1 + i = i + 1 by omega]⟩
  | t + 1 => encF_step hF (win_enc hF t)

/-- The last two readings of column 1 at the first white steps (newest in bit 0), starting from `0`. -/
def suf (ph : Nat) (F : Nat → Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => sNext ((t + ph) % 7) (suf ph F t) (win F t)

theorem suf_lt (ph : Nat) (F : Nat → Nat → Bool) : ∀ t, suf ph F t < 4
  | 0 => Nat.zero_lt_succ _
  | t + 1 => by
    show sNext _ _ _ < 4
    unfold sNext
    cases ((t + ph) % 7 == 0)
    · exact suf_lt ph F t
    · exact Nat.mod_lt _ (by decide)

theorem sNext_ne {p s w : Nat} (h : p ≠ 0) : sNext p s w = s := by
  simp [sNext, h]

/-- One more reading. -/
def push (s : Nat) (a : Bool) : Nat := (2 * s + a.toNat) % 4

section Driven

variable (R : Nat → Bool) (ph : Nat)

theorem win_succ (t : Nat) :
    win (drv (ctr ph) R) (t + 1) = wNext ((t + ph) % 7) (win (drv (ctr ph) R) t) (drv (ctr ph) R t 11) := by
  show stripStep 10 (drv (ctr ph) R t 0) _ _ = stripStep _ _ _ _
  rw [drv_col0]
  rfl

theorem state_ok (t : Nat) :
    nodeOK ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = true :=
  node_ok (Nat.mod_lt _ (by decide)) (suf_lt _ _ _) (win_enc (drv_isR30 _ _) t).1

/-- **Rank bound.** Along the driven right half the rank at time `t` is at most `35 - t`. -/
theorem rank_bound : ∀ t, rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) ≤ 35 - t
  | 0 => (node_facts (state_ok R ph 0) false).1
  | t + 1 => by
    have ih := rank_bound t
    have hf := node_facts (state_ok R ph t) (drv (ctr ph) R t 11)
    rw [← win_succ] at hf
    have hp : (t + 1 + ph) % 7 = ((t + ph) % 7 + 1) % 7 := by omega
    have hs : suf ph (drv (ctr ph) R) (t + 1) =
        sNext ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) := rfl
    rw [hp, hs]
    by_cases h0 : rk ((t + ph) % 7) (suf ph (drv (ctr ph) R) t) (win (drv (ctr ph) R) t) = 0
    · rw [(hf.2.1 h0).1]; exact Nat.zero_le _
    · have := hf.2.2 h0; omega

/-- From time 35 on, no reading at the first white steps completes a forbidden word. -/
theorem no_bad (t : Nat) (ht : 35 ≤ t) (hp : (t + ph) % 7 = 0) :
    badB (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) = false := by
  have h0 := rank_bound R ph t
  have hf := node_facts (state_ok R ph t) false
  have hb := (hf.2.1 (by omega)).2 hp
  rwa [encF_head (win_enc (drv_isR30 _ _) t) (by decide)] at hb

/-- The readings move one place at each first white step. -/
theorem suf_period (t : Nat) (hp : (t + ph) % 7 = 0) :
    suf ph (drv (ctr ph) R) (t + 7) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
  have h1 : suf ph (drv (ctr ph) R) (t + 1) = push (suf ph (drv (ctr ph) R) t) (drv (ctr ph) R t 1) := by
    show sNext ((t + ph) % 7) _ _ = _
    rw [hp]
    unfold sNext push
    rw [encF_head (win_enc (drv_isR30 _ _) t) (by decide)]
    rfl
  have h2 : suf ph (drv (ctr ph) R) (t + 2) = suf ph (drv (ctr ph) R) (t + 1) := by
    show sNext ((t + 1 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 1)) (win (drv (ctr ph) R) (t + 1)) = _
    exact sNext_ne (by omega)
  have h3 : suf ph (drv (ctr ph) R) (t + 3) = suf ph (drv (ctr ph) R) (t + 2) := by
    show sNext ((t + 2 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 2)) (win (drv (ctr ph) R) (t + 2)) = _
    exact sNext_ne (by omega)
  have h4 : suf ph (drv (ctr ph) R) (t + 4) = suf ph (drv (ctr ph) R) (t + 3) := by
    show sNext ((t + 3 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 3)) (win (drv (ctr ph) R) (t + 3)) = _
    exact sNext_ne (by omega)
  have h5 : suf ph (drv (ctr ph) R) (t + 5) = suf ph (drv (ctr ph) R) (t + 4) := by
    show sNext ((t + 4 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 4)) (win (drv (ctr ph) R) (t + 4)) = _
    exact sNext_ne (by omega)
  have h6 : suf ph (drv (ctr ph) R) (t + 6) = suf ph (drv (ctr ph) R) (t + 5) := by
    show sNext ((t + 5 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 5)) (win (drv (ctr ph) R) (t + 5)) = _
    exact sNext_ne (by omega)
  have h7 : suf ph (drv (ctr ph) R) (t + 7) = suf ph (drv (ctr ph) R) (t + 6) := by
    show sNext ((t + 6 + ph) % 7) (suf ph (drv (ctr ph) R) (t + 6)) (win (drv (ctr ph) R) (t + 6)) = _
    exact sNext_ne (by omega)
  rw [h7, h6, h5, h4, h3, h2, h1]

end Driven

/-! ### The forbidden words -/

theorem bad_11 : ∀ s, s < 4 → badB (push s true) true = true := by decide
theorem bad_101 : ∀ s, s < 4 → badB (push (push s true) false) true = true := by decide

end ReadingWords.B0110111

open ReadingWords.B0110111

section Driven

variable (R : Nat → Bool) (ph : Nat)

/-- **No `11`.** At the first white steps, column 1 never reads `11` with the first reading at time `28` or
later. -/
theorem no_11_time_0110111 (u : Nat) (hu : 28 ≤ u) (hp : (u + ph) % 7 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 7) 1 = true) := by
  rintro ⟨h0, h1⟩
  have hb := no_bad R ph (u + 7) (by omega) (by omega)
  rw [suf_period R ph u hp, h0, h1] at hb
  rw [bad_11 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

/-- **No `101`.** At the first white steps, column 1 never reads `101` with the first reading at time `21` or
later. -/
theorem no_101_time_0110111 (u : Nat) (hu : 21 ≤ u) (hp : (u + ph) % 7 = 0) :
    ¬ (drv (ctr ph) R u 1 = true ∧ drv (ctr ph) R (u + 7) 1 = false ∧ drv (ctr ph) R (u + 14) 1 = true) := by
  rintro ⟨h0, h1, h2⟩
  rw [show u + 14 = u + 7 + 7 by omega] at h2
  have hb := no_bad R ph (u + 7 + 7) (by omega) (by omega)
  rw [suf_period R ph (u + 7) (by omega), suf_period R ph u hp, h0, h1, h2] at hb
  rw [bad_101 _ (suf_lt _ _ _)] at hb
  exact absurd hb (by decide)

end Driven

/-! ### The readings as a sequence -/

namespace ReadingWords.B0110111

/-- A sequence of bits has none of the factors `11`, `101` from index `i0` on. -/
def Avoids (b : Nat → Bool) (i0 : Nat) : Prop :=
  ∀ i, i0 ≤ i → ¬ (b i = true ∧ b (i + 1) = true) ∧
    ¬ (b i = true ∧ b (i + 1) = false ∧ b (i + 2) = true)

/-- Column 1 of the right half driven by `0110111` from phase `ph`, at the `i`-th first white step (the steps `t` with
`(t + ph) % 7 = 0`). -/
def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (7 * i + (7 - ph % 7) % 7) 1

end ReadingWords.B0110111

/-- **Readings.** For every right half `R` and phase `ph`, the readings of column 1 at the first white steps avoid
`11`, `101` from the 4th on. -/
theorem readings_0110111 (R : Nat → Bool) (ph : Nat) : Avoids (reading R ph) 4 := by
  intro i hi
  have hp : (7 * i + (7 - ph % 7) % 7 + ph) % 7 = 0 := by omega
  have e1 : reading R ph (i + 1) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 7) 1 := by
    unfold reading; rw [show 7 * (i + 1) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 7 by omega]
  have e2 : reading R ph (i + 2) = drv (ctr ph) R (7 * i + (7 - ph % 7) % 7 + 14) 1 := by
    unfold reading; rw [show 7 * (i + 2) + (7 - ph % 7) % 7 = 7 * i + (7 - ph % 7) % 7 + 14 by omega]
  rw [e1, e2]
  exact ⟨no_11_time_0110111 R ph _ (by omega) hp, no_101_time_0110111 R ph _ (by omega) hp⟩

/-! ### Every row whose center column repeats `0110111` -/

namespace ReadingWords.B0110111

/-- From time `T` on, a row whose center column repeats `0110111` from `T` has the right half driven by `0110111` from
phase `0`, started from its own right half at time `T`. -/
theorem evolve_eq_drv (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0110111.getD ((t - T) % 7) false) :
    ∀ t p : Nat, evolve init (T + t) (p : Int) = drv (ctr 0) (fun p => evolve init T (p : Int)) t p
  | 0, 0 => by
    rw [drv_col0]
    show evolve init (T + 0) 0 = w0110111.getD ((0 + 0) % 7) false
    rw [Nat.add_zero, h T (Nat.le_refl T), Nat.sub_self]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by
    rw [drv_col0]
    show evolve init (T + (t + 1)) 0 = w0110111.getD ((t + 1 + 0) % 7) false
    rw [h (T + (t + 1)) (by omega), show T + (t + 1) - T = t + 1 + 0 by omega]
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule30 (evolve init (T + t) (((q + 1 : Nat) : Int) - 1)) (evolve init (T + t) ((q + 1 : Nat) : Int))
        (evolve init (T + t) (((q + 1 : Nat) : Int) + 1)) =
      Rule30Jen.rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← evolve_eq_drv init T h t q, ← evolve_eq_drv init T h t (q + 1), ← evolve_eq_drv init T h t (q + 2),
      show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega,
      show ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) by omega]
    rfl

end ReadingWords.B0110111

/-- **Readings of every row.** If the center column of a row repeats `0110111` from time `T` (letter
`(t - T) % 7` at time `t`), then column 1 at the times `T + 7 i` avoids `11`, `101` from `i = 4` on. -/
theorem readings_0110111_evolve (init : Int → Bool) (T : Nat)
    (h : ∀ t, T ≤ t → evolve init t 0 = w0110111.getD ((t - T) % 7) false) :
    Avoids (fun i => evolve init (T + 7 * i) 1) 4 := by
  have e : (fun i => evolve init (T + 7 * i) 1) = reading (fun p => evolve init T (p : Int)) 0 := by
    funext i
    rw [show T + 7 * i = T + (7 * i + (7 - 0 % 7) % 7) by omega]
    exact evolve_eq_drv init T h (7 * i + (7 - 0 % 7) % 7) 1
  rw [e]
  exact readings_0110111 _ 0

end B0110111

end Rule30Open
