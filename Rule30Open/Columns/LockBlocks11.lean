module

public import Rule30Open.Columns.LockBlocks

/-!
# Steering sequences force locks for 26 blocks of period 4 to 11

[LockBlocks](LockBlocks.md) turns a check the kernel evaluates, `lockCheckB`, into a lock of the finite game: once the
center column repeats a block, column 14 never reads a steering sequence. Here the check runs on the 26 blocks of
period 4 to 11 that neither the game at width 14 nor the kit excludes and whose game at width 13 has locked windows
that every window can be steered into, from `computations/locks.py`.

* `steered11`: the entries `Steered`, each block as its least rotation with its sequence and the windows where the
  sequence leaves each start; `steered11_check`: every check passes.
* `center_lock_steered11`: once the center column repeats one of the blocks from time `T`, read from any phase,
  column 14 does not read the block's sequence from any time `t₀ ≥ T`.
* `not_eventually_steered11`: so if column 14 reads the sequence at arbitrarily late times, the center column does
  not eventually repeat the block, in the kit's form `EventuallyWord`.

The natural-language argument is `LockBlocks11.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata LockWord LockBlocks

namespace LockBlocks

set_option Elab.async false

def steer_0111 : Steered := ⟨4, 0b0111,
  0x640094032008190040c8020541200d032001304840812c31068926544dca82cc440acc4444c22ee6d,
  323, [(0, [3690, 4202, 4714, 6308]), (1, [4286, 4542, 6059, 8107, 8126]), (2, [168, 3496, 5856, 6530]), (3, [1965,
    3782, 4525, 8134])]⟩

set_option maxHeartbeats 0 in
theorem steer_0111_check : steer_0111.check = true := by decide +kernel

def steer_00000101 : Steered := ⟨8, 0b00000101,
  0x200000080000000100000320019000804000208083100000000012811342854a860101157323a28a4fff83a703f39ca,
  398, [(0, [4690]), (1, [1375]), (2, [65, 7331]), (3, [227, 5475]), (4, [309, 5429]), (5, [981]), (6, [1108]), (7,
    [3798])]⟩

set_option maxHeartbeats 0 in
theorem steer_00000101_check : steer_00000101.check = true := by decide +kernel

def steer_00011101 : Steered := ⟨8, 0b00011101,
  0x11000c00011000c0004400300004400300002200180000100000000200400000030000080094010020000080200000800040040000002026008004000000080200002040010810004004080400800400040010001008002008002004002004001000000400000060000c68056f1eafe,
  903, [(0, [2509, 6989]), (1, [5877, 5983, 7797]), (2, [4629]), (3, [245, 5717]), (4, [3860, 5268]), (5, [503, 6135]),
    (6, [2000, 2576]), (7, [2808, 4088])]⟩

set_option maxHeartbeats 0 in
theorem steer_00011101_check : steer_00011101.check = true := by decide +kernel

def steer_00011111 : Steered := ⟨8, 0b00011111,
  0x4422804000004200004400080020180050a00040400300a000000004aa560e58afadf,
  280, [(0, [2602, 4970]), (1, [5803, 7019]), (2, [1513, 1705, 3241, 6441, 7721]), (3, [2735, 3567, 5158, 8175]), (4,
    [1312, 4128]), (5, [2225, 3697]), (6, [26, 1690, 2714, 7322]), (7, [490, 938, 1258, 2794, 7402])]⟩

set_option maxHeartbeats 0 in
theorem steer_00011111_check : steer_00011111.check = true := by decide +kernel

def steer_00111101 : Steered := ⟨8, 0b00111101,
  0x884001108020021128800110800ac26007004c1981c0099f3424c3a24c51e447c1d98b9b9b9343c3f3d,
  332, [(0, [2056, 7432]), (1, [44, 3100, 6140, 6700]), (2, [870, 3750, 6950, 7206]), (3, [1658, 1722, 3258]), (4, [458,
    4042, 4234, 4554, 5002, 7306]), (5, [378, 1434, 5726, 6778]), (6, [234, 4874, 6282, 6474]), (7, [2267, 4827, 6395,
    7339])]⟩

set_option maxHeartbeats 0 in
theorem steer_00111101_check : steer_00111101.check = true := by decide +kernel

def steer_00111111 : Steered := ⟨8, 0b00111111,
  0x1800404020e0202123c,
  93, [(0, [250, 850, 1290, 1682, 1786, 1794, 2090, 2362, 2562, 2962, 4098, 5194, 5242, 5962, 6034, 6594, 6658, 6858,
    7354, 7442, 7618, 8002]), (1, [267, 359, 641, 1195, 1375, 1471, 1931, 2439, 2571, 2815, 2823, 2923, 3687, 4351,
    4747, 5771, 5883, 6151, 7899, 8139]), (2, [121, 825, 921, 1337, 1401, 1705, 2265, 2441, 2561, 3081, 3257, 3393,
    4009, 4617, 4825, 6401, 6537, 6921, 6937, 7049, 7809, 7897, 7933]), (3, [142, 478, 516, 706, 910, 1262, 1486, 2270,
    2462, 2478, 2734, 3342, 3806, 3970, 4482, 5474, 5506, 6030, 6082, 6914, 7310, 7502]), (4, [418, 466, 1234, 1638,
    1807, 2034, 3186, 3330, 3874, 4198, 4294, 4674, 4898, 5318, 6562, 6818, 7330, 7490, 7842, 7890]), (5, [566, 694,
    926, 1054, 2022, 2078, 2142, 2742, 3358, 3786, 3934, 4598, 5586, 5790, 5994, 6262, 7670, 7882, 7966, 8166]), (6,
    [58, 1042, 1546, 1682, 1874, 1986, 2106, 2194, 2466, 2706, 3218, 3386, 3466, 3882, 3906, 4394, 4562, 5214, 5890,
    6034, 6282, 6674, 7202, 7442]), (7, [74, 694, 1654, 1894, 2398, 2510, 2814, 2878, 3166, 4454, 5086, 5302, 5826,
    6010, 6910, 6918, 7014, 7146, 7242, 7734])]⟩

set_option maxHeartbeats 0 in
theorem steer_00111111_check : steer_00111111.check = true := by decide +kernel

def steer_0000000101 : Steered := ⟨10, 0b0000000101,
  0x4830000404c008000000000000802184849414140414a6f07870d253a,
  254, [(0, [82]), (1, [223, 2287]), (2, [321]), (3, [867]), (4, [1333]), (5, [3541]), (6, [5205]), (7, [5845]), (8,
    [4692]), (9, [1366, 8150])]⟩

set_option maxHeartbeats 0 in
theorem steer_0000000101_check : steer_0000000101.check = true := by decide +kernel

def steer_0000011101 : Steered := ⟨10, 0b0000011101,
  0x50023080000000528000001000014a00000300061000000030800848002032000040640021200608182c0c010008040301c050640d17c3b9,
  449, [(0, [3405, 4685]), (1, [5493, 7157]), (2, [21, 1813, 5397]), (3, [2291, 2805, 3125, 3509]), (4, [1557, 5269]),
    (5, [3285, 6133]), (6, [3412, 6676, 7636]), (7, [4439, 7223]), (8, [1488, 2512]), (9, [3288, 5848, 7000])]⟩

set_option maxHeartbeats 0 in
theorem steer_0000011101_check : steer_0000011101.check = true := by decide +kernel

def steer_0001111111 : Steered := ⟨10, 0b0001111111,
  0x60000098024b041982d90c489b1160f0d71915555d7cdae3ef6e0b4ae3e452e3b82eb,
  275, [(0, [3754, 5418, 7210]), (1, [1963, 2923, 5611]), (2, [41, 1065, 2345, 6313]), (3, [4207, 4483, 6575, 7343]),
    (4, [32, 3744, 6034, 7072]), (5, [6577]), (6, [1946, 5018, 6298]), (7, [1258]), (8, [3370, 5674, 7978]), (9, [874,
    4970])]⟩

set_option maxHeartbeats 0 in
theorem steer_0001111111_check : steer_0001111111.check = true := by decide +kernel

def steer_0011111101 : Steered := ⟨10, 0b0011111101,
  0x2885000021080000000800401419004010007516dfae77,
  199, [(0, [744, 1576, 2280, 2920, 7016, 7912]), (1, [1580, 2348, 2924, 4972, 5532, 6444, 6700]), (2, [422, 977, 1510,
    1958, 5350, 6054, 7462, 8166]), (3, [698, 1530, 4154, 5946, 6458]), (4, [3978, 4042, 4106, 4554, 6218, 6410, 7562]),
    (5, [122, 250, 3994, 4218, 5658, 6522, 6778]), (6, [2634, 2954, 3914, 4330, 4593, 4906]), (7, [922, 3546, 4474,
    5738, 5930, 6362, 7162]), (8, [1066, 2858, 3402, 5194, 6922]), (9, [27, 2459, 3099, 3691, 5499, 7195])]⟩

set_option maxHeartbeats 0 in
theorem steer_0011111101_check : steer_0011111101.check = true := by decide +kernel

def steer_0111011111 : Steered := ⟨10, 0b0111011111,
  0x4802224011904804000120100120006d200880400480404200420480480403080a046102120119210a00001120490519200a009842e01485ca0382698d27146315212cdd44b04c1db264efc78dc3f8dd3aff,
  655, [(0, [2218]), (1, [4171, 8107]), (2, [168, 1192]), (3, [8109]), (4, [4260]), (5, [5822]), (6, [3714]), (7,
    [5830]), (8, [2666]), (9, [938])]⟩

set_option maxHeartbeats 0 in
theorem steer_0111011111_check : steer_0111011111.check = true := by decide +kernel

def steer_00000000101 : Steered := ⟨11, 0b00000000101,
  0x2010101418820500922261dfa33085d0dcf8b474f3388710721fd3f6,
  222, [(0, [4306]), (1, [3039, 4447]), (2, [4929]), (3, [5475]), (4, [7477]), (5, [1493, 5589]), (6, [7253]), (7,
    [4803, 7893]), (8, [341, 1173, 4693]), (9, [5956, 7892, 8148]), (10, [1878])]⟩

set_option maxHeartbeats 0 in
theorem steer_00000000101_check : steer_00000000101.check = true := by decide +kernel

def steer_00000011101 : Steered := ⟨11, 0b00000011101,
  0x2000000000000220402a05a404a6902f,
  141, [(0, [77, 1101, 2381, 4685, 8141]), (1, [117, 2165, 3829, 5493, 8181]), (2, [149, 2325, 4629, 5397, 8085]), (3,
    [53, 501, 949, 2291]), (4, [85, 277, 469, 533, 1173, 3221, 5269]), (5, [213, 949, 1845, 6133]), (6, [1173, 1493,
    2517, 4117]), (7, [3284, 4084, 6196, 7764]), (8, [983, 2519, 3159, 4951]), (9, [1104, 3664, 5840, 7504]), (10,
    [3160, 3800, 4696, 7000])]⟩

set_option maxHeartbeats 0 in
theorem steer_00000011101_check : steer_00000011101.check = true := by decide +kernel

def steer_00000110001 : Steered := ⟨11, 0b00000110001,
  0x180c010006080000002a8180c010006080000000e03004001820000000200c060080030400000014c00510008c00500888800c060080030400000015300144002000184010820004603004001820c00500b01802000c100000005300144002600288004000301802000c16030040018200000003c2008410002301802000c10300144003001440030180200301803001402030014020c0051000c00500838400044c0050038580d19909838c1a6100007,
  1409, [(0, [3866]), (1, [1451]), (2, [4777]), (3, [2735]), (4, [4769]), (5, [2739]), (6, [2716]), (7, [2791]), (8,
    [2617]), (9, [2895, 4479]), (10, [2417])]⟩

set_option maxHeartbeats 0 in
theorem steer_00000110001_check : steer_00000110001.check = true := by decide +kernel

def steer_00000110011 : Steered := ⟨11, 0b00000110011,
  0x100d0100000000643600086010201a00204051230a80406980aa417e40a3280a2664a8a2331554230082a24940e2d2a3024ec18f3cdd93018279b5bfaa3a5de582eb3f499a,
  554, [(0, [1405]), (1, [4731, 7941]), (2, [397]), (3, [725]), (4, [5973]), (5, [4437]), (6, [6996]), (7, [2391]), (8,
    [849]), (9, [347]), (10, [840])]⟩

set_option maxHeartbeats 0 in
theorem steer_00000110011_check : steer_00000110011.check = true := by decide +kernel

def steer_00001001101 : Steered := ⟨11, 0b00001001101,
  0x102300000000000044000008a0000000000000020080000000000000000000044004c40080000000000000000000020000001400400000000000000000000000000005001000040000000000000000000000014004000000000000000000000000000000000000000080502e,
  863, [(0, [5422]), (1, [4579]), (2, [1171, 5173, 7733]), (3, [4949, 5717]), (4, [3829, 5077, 7509]), (5, [3924,
    7252]), (6, [342, 1750]), (7, [2643, 3411, 4243]), (8, [1372, 7132]), (9, [5447, 6215]), (10, [361, 3305])]⟩

set_option maxHeartbeats 0 in
theorem steer_00001001101_check : steer_00001001101.check = true := by decide +kernel

def steer_00001101011 : Steered := ⟨11, 0b00001101011,
  0x184311005400000000280a000000006002a280000001400060050184355550000000200000210000000000000000000000000000000000000000000005401007a,
  513, [(0, [909, 1293, 1965]), (1, [5013, 5333]), (2, [5365, 7413]), (3, [5909, 6485]), (4, [717, 4533, 5957, 7925]),
    (5, [116, 340, 3924]), (6, [2807, 2967, 3927]), (7, [337, 2577]), (8, [4154, 5466]), (9, [2507, 3019, 5451]), (10,
    [3704, 4984])]⟩

set_option maxHeartbeats 0 in
theorem steer_00001101011_check : steer_00001101011.check = true := by decide +kernel

def steer_00001111111 : Steered := ⟨11, 0b00001111111,
  0x80000000080000000080000000010000000000800000000000000000040085b0,
  289, [(0, [3010, 5162, 6442]), (1, [359, 1899, 4075, 4747, 7019]), (2, [825, 2345, 5433]), (3, [591, 1487, 5583, 6031,
    8175]), (4, [1953, 4305, 4603]), (5, [114, 2226, 5786]), (6, [158, 3914, 7582]), (7, [1642, 2850, 7722]), (8, [222,
    566, 6922, 7774]), (9, [962, 1322, 4562]), (10, [870, 2398, 3562, 7518])]⟩

set_option maxHeartbeats 0 in
theorem steer_00001111111_check : steer_00001111111.check = true := by decide +kernel

def steer_00011111111 : Steered := ⟨11, 0b00011111111,
  0x11440044088126146102083560128165027111a701a1c0a270c8c14614de3670a2bc91c4f107ba9,
  314, [(0, [2730, 4074, 6058, 7338]), (1, [1963, 2219, 5751, 7211, 7879]), (2, [105, 1865]), (3, [3503, 5039, 5807]),
    (4, [3744, 6560]), (5, [2225, 2737]), (6, [2202, 3378]), (7, [3818]), (8, [42, 3626]), (9, [490, 2922, 4074]), (10,
    [4394, 6442])]⟩

set_option maxHeartbeats 0 in
theorem steer_00011111111_check : steer_00011111111.check = true := by decide +kernel

def steer_00101101111 : Steered := ⟨11, 0b00101101111,
  0xa208200a0000250080000144101040100500000a208082008028000101030800890000000808184111500000005104044040004002020610008081841115000000a20808808000008808c00020206000000008081800004040c2088a8002029000440501200004040c0002020600028002202809000220230004040c000000044050120004040c00080a4001101180010103000020206000080818000220230004040c00008081800040520008808c0008808c0008081800101030002020600040520004040c00202060010148001010300000000036,
  1725, [(0, [682, 7722]), (1, [1707, 5275]), (2, [2729]), (3, [3566]), (4, [2723]), (5, [5748]), (6, [663, 5015]), (7,
    [6897]), (8, [1818, 2586]), (9, [2474]), (10, [7850])]⟩

set_option maxHeartbeats 0 in
theorem steer_00101101111_check : steer_00101101111.check = true := by decide +kernel

def steer_00110011111 : Steered := ⟨11, 0b00110011111,
  0xc08000000006040044000000821c080a000c8001200c002880008880000000a46810a6821a18c028c6a69a6894cd71620acb6a925b0a5b6f78bda8b3f0f05b4f8046bb28b6fadacefd6947a1f27,
  620, [(0, [3754]), (1, [683]), (2, [5801]), (3, [4782]), (4, [5794]), (5, [2743]), (6, [2705]), (7, [2810]), (8,
    [2570]), (9, [2842, 5186]), (10, [2474])]⟩

set_option maxHeartbeats 0 in
theorem steer_00110011111_check : steer_00110011111.check = true := by decide +kernel

def steer_00111111101 : Steered := ⟨11, 0b00111111101,
  0x10000100004000100001000040001000000000410c0400b84e85f7fec55,
  250, [(0, [1704, 2920, 4824, 4968]), (1, [4908, 6444, 7468]), (2, [1014, 1510, 4070]), (3, [1042, 3130, 6586]), (4,
    [3646, 3658, 5706, 6218]), (5, [3194, 3994, 4930, 5114]), (6, [5898, 7178, 7526]), (7, [1338, 4826, 6442, 8186]),
    (8, [3530, 4362, 6890, 7178]), (9, [2458, 5242, 6634, 7338]), (10, [427, 4239, 7915])]⟩

set_option maxHeartbeats 0 in
theorem steer_00111111101_check : steer_00111111101.check = true := by decide +kernel

def steer_01010101011 : Steered := ⟨11, 0b01010101011,
  0x1000000010224840400042020001000000000000001000010c410000001880004000000020000002000000108200003022000082020100100040000a0044c011d33e06,
  534, [(0, [1322, 7338]), (1, [3563, 6059]), (2, [2216, 5160]), (3, [5740, 6572]), (4, [3751, 5031]), (5, [1846, 4793,
    7353]), (6, [1678, 1934]), (7, [723, 2259]), (8, [1628, 3420]), (9, [5062, 5446]), (10, [2154, 3434])]⟩

set_option maxHeartbeats 0 in
theorem steer_01010101011_check : steer_01010101011.check = true := by decide +kernel

def steer_01011111011 : Steered := ⟨11, 0b01011111011,
  0x891550000001000008220000448aa8000000800221100000040000004000000001108800000020000001000000010000000800000040000000400000020000001000000010000000800000040000000000000000011472,
  711, [(0, [6573]), (1, [1619, 3749, 5349]), (2, [5948]), (3, [4550]), (4, [714, 2410]), (5, [1658, 2986, 6522]), (6,
    [490, 2954]), (7, [3498]), (8, [3402]), (9, [5499, 6443]), (10, [8168])]⟩

set_option maxHeartbeats 0 in
theorem steer_01011111011_check : steer_01011111011.check = true := by decide +kernel

def steer_01110111111 : Steered := ⟨11, 0b01110111111,
  0x880100002024000021353463510832eaea800000344c04202012040002ebefd40209c01c6222d4a2a88601c88444130823d57af6fdf6be9fa3,
  466, [(0, [7594]), (1, [1195, 5315]), (2, [4008]), (3, [4269]), (4, [6564]), (5, [3774]), (6, [4738]), (7, [7878]),
    (8, [2666]), (9, [1962, 2986]), (10, [2218])]⟩

set_option maxHeartbeats 0 in
theorem steer_01110111111_check : steer_01110111111.check = true := by decide +kernel

def steer_01111011111 : Steered := ⟨11, 0b01111011111,
  0x8488000110001091000022000000212200004400084880080000084880080000084880080000000000000424400008800212200200000000000001091001000000000000008488008000008488008000000000000000914600130000000000008488040110000000000008020900010000000000001091008022000000000080209000122800000000000000000000000000000010910802200000001228001228000000000002000000000091400091400000000000000000000000000000000000000000000000000000000000020018700040c0600207c7,
  1749, [(0, [2382]), (1, [8051]), (2, [284, 6940]), (3, [1447]), (4, [1208]), (5, [3981]), (6, [4309, 7907]), (7,
    [6484]), (8, [3927]), (9, [4432]), (10, [7001])]⟩

set_option maxHeartbeats 0 in
theorem steer_01111011111_check : steer_01111011111.check = true := by decide +kernel

end LockBlocks

/-- The 26 blocks of period 4 to 11 that neither the game at width 14 nor the kit excludes and whose game at width 13
has locked windows that every window can be steered into, as entries `Steered`. -/
def steered11 : List Steered := [
    steer_0111, steer_00000101, steer_00011101, steer_00011111, steer_00111101, steer_00111111, steer_0000000101,
    steer_0000011101, steer_0001111111, steer_0011111101, steer_0111011111, steer_00000000101, steer_00000011101,
    steer_00000110001, steer_00000110011, steer_00001001101, steer_00001101011, steer_00001111111, steer_00011111111,
    steer_00101101111, steer_00110011111, steer_00111111101, steer_01010101011, steer_01011111011, steer_01110111111,
    steer_01111011111]

/-- Every check passes. -/
theorem steered11_check : ∀ e ∈ steered11, e.check = true := by
  intro e he
  simp only [steered11, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact steer_0111_check
  · exact steer_00000101_check
  · exact steer_00011101_check
  · exact steer_00011111_check
  · exact steer_00111101_check
  · exact steer_00111111_check
  · exact steer_0000000101_check
  · exact steer_0000011101_check
  · exact steer_0001111111_check
  · exact steer_0011111101_check
  · exact steer_0111011111_check
  · exact steer_00000000101_check
  · exact steer_00000011101_check
  · exact steer_00000110001_check
  · exact steer_00000110011_check
  · exact steer_00001001101_check
  · exact steer_00001101011_check
  · exact steer_00001111111_check
  · exact steer_00011111111_check
  · exact steer_00101101111_check
  · exact steer_00110011111_check
  · exact steer_00111111101_check
  · exact steer_01010101011_check
  · exact steer_01011111011_check
  · exact steer_01110111111_check
  · exact steer_01111011111_check

/-- **The 26 blocks**: once the center column repeats the block of an entry of `steered11` from time `T`, read
from phase `shift`, column 14 does not read the entry's sequence from any time `t₀ ≥ T`. -/
theorem center_lock_steered11 (e : Steered) (he : e ∈ steered11) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.period e.bits).getD ((t + shift) % e.period) false) (t0 : Nat)
    (ht0 : T ≤ t0) : ∃ i, i < e.len ∧ Rule30Jen.cell (t0 + i) 14 ≠ e.seq.testBit i :=
  center_lock_steered e (steered11_check e he) T shift h t0 ht0

/-- **The sufficient condition**: if column 14 reads the sequence of an entry of `steered11` at arbitrarily late
times, the center column does not eventually repeat the entry's block. -/
theorem not_eventually_steered11 (e : Steered) (he : e ∈ steered11)
    (hw : ∀ N, ∃ t0, N ≤ t0 ∧ ∀ i, i < e.len → Rule30Jen.cell (t0 + i) 14 = e.seq.testBit i) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.period e.bits) :=
  not_eventually_steered e (steered11_check e he) hw

end Rule30Open
