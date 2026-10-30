module

public import Rule30Open.Columns.LockBlocks

/-!
# A white run beside a window forces a lock, for 22 blocks

For 22 of the blocks of [LockBlocks11](LockBlocks11.md) and [LockBlocks12](LockBlocks12.md), a run of white values
in the column beyond a window of `width` cells brings every window, started at any phase, to a locked window. So once
the center column repeats such a block, that column is black at least once in every stretch of that many steps. The
shortest run is 27 values in column 8, for `000011111111`.

* `WhiteRun`, `WhiteRun.check`: an entry is a block, a width, a number of white values and the windows where the run
  leaves each start; its check is `lockCheckB` with the white sequence.
* `center_white_run`: for an entry whose check passes, once the center repeats the block from time `T`, read from any
  phase, column `width + 1` is black at some time in every stretch of `len` steps from `T` on.
* `whiteRuns`, `whiteRuns_check`, `center_white_runs`, `not_eventually_white_runs`: the 22 entries, the blocks whose
  shortest steering run over the widths 4 to 16 comes at a width of at most 13, from `computations/locks.py`; every
  check passes; and so if that column has `len` white cells in a row at arbitrarily late times, the center column does
  not eventually repeat the block, in the kit's form `EventuallyWord`.

The natural-language argument is `LockWhite.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata LockWord LockBlocks

namespace LockBlocks

/-- A block `wordOf period bits` for which `len` white values of the column beyond a window of `width` cells bring
every window, started at any phase, to a locked window, with the windows where they leave each start, by final
phase. -/
structure WhiteRun where
  period : Nat
  bits : Nat
  width : Nat
  len : Nat
  groups : List (Nat × List Nat)

/-- `lockCheckB` for the entry with the white sequence, with search fuel 300. -/
def WhiteRun.check (e : WhiteRun) : Bool :=
  lockCheckB (Rule30StripCertificateTable.wordOf e.period e.bits) e.width (bitsOf 0 e.len) e.groups 300

set_option Elab.async false

def white_00000101 : WhiteRun := ⟨8, 0b00000101,
  12, 130, [(0, [338, 594, 850, 1106, 2130, 2642, 3026]), (1, [863, 1375, 2015, 2143, 3039, 3295, 3807]), (2, [577,
    1345, 1857, 2113, 3265, 3393]), (3, [1379, 1891, 2019, 2403, 3299, 3427]), (4, [1333, 1845, 2101, 2197, 2357, 3381,
    3893]), (5, [469, 1493, 2517, 3157, 3541, 3573, 4053]), (6, [84, 596, 1044, 1108, 1748, 3156, 3668]), (7, [214, 982,
    1750, 2006, 2646, 3638, 3798])]⟩

set_option maxHeartbeats 0 in
theorem white_00000101_check : white_00000101.check = true := by decide +kernel

def white_00111101 : WhiteRun := ⟨8, 0b00111101,
  9, 85, [(0, [24, 72, 168, 232, 264, 408]), (1, [44, 236, 252, 300, 412, 428]), (2, [102, 166, 230, 262, 294, 486]),
    (3, [58, 186, 314, 394, 442, 506]), (4, [10, 74, 138, 218, 394, 458]), (5, [26, 122, 218, 250, 330, 474]), (6, [6,
    42, 74, 138, 266, 330, 378]), (7, [11, 107, 251, 267, 379, 411, 475])]⟩

set_option maxHeartbeats 0 in
theorem white_00111101_check : white_00111101.check = true := by decide +kernel

def white_00111111 : WhiteRun := ⟨8, 0b00111111,
  12, 66, [(0, [2, 42, 130, 194, 514, 1098, 1258, 1786, 1810, 1938, 1978, 2426, 2562, 2662, 2822, 2898, 2962, 3194,
    3602]), (1, [7, 107, 359, 455, 615, 831, 1675, 1799, 2099, 2187, 2303, 2399, 2443, 2495, 2571, 2823, 3003, 3835,
    3851, 3883]), (2, [9, 169, 409, 489, 521, 617, 825, 1473, 1977, 2185, 2441, 2777, 2841, 3165, 3329, 3545, 3713,
    3801, 3905]), (3, [30, 354, 430, 558, 590, 706, 750, 1102, 1410, 1486, 1732, 1822, 1966, 2190, 2478, 2638, 3170,
    3550, 3806, 4014]), (4, [34, 162, 578, 674, 822, 1090, 1394, 1570, 1638, 1718, 1890, 2034, 2210, 2466, 2671, 3058,
    3186, 3270, 3538, 3746, 3826]), (5, [118, 438, 542, 694, 1118, 1490, 1694, 1718, 1898, 2022, 2078, 2358, 2706, 2934,
    2976, 3002, 3358, 3510, 3766, 3814]), (6, [146, 570, 658, 1170, 1442, 1682, 1826, 2106, 2186, 2225, 2322, 2346,
    2706, 2786, 2814, 3106, 3166, 3778, 4050]), (7, [94, 510, 614, 1482, 1654, 1730, 1790, 1866, 2550, 2562, 2614, 2814,
    3146, 3254, 3482, 3546, 4030, 4074, 4094])]⟩

set_option maxHeartbeats 0 in
theorem white_00111111_check : white_00111111.check = true := by decide +kernel

def white_0001111111 : WhiteRun := ⟨10, 0b0001111111,
  12, 92, [(0, [426, 682, 2346]), (1, [683, 1707, 4075]), (2, [41, 1705, 2729]), (3, [111, 2735, 3446]), (4, [160, 1298,
    1568, 2720]), (5, [433, 2737, 2929, 3518]), (6, [666, 1154, 2330, 2714]), (7, [1770, 2794, 4010, 4038]), (8, [106,
    170, 2602]), (9, [170, 426, 2922])]⟩

set_option maxHeartbeats 0 in
theorem white_0001111111_check : white_0001111111.check = true := by decide +kernel

def white_0011111101 : WhiteRun := ⟨10, 0b0011111101,
  9, 86, [(0, [232, 264, 488]), (1, [44, 300, 412]), (2, [102, 230, 465, 486]), (3, [58, 90, 186, 314]), (4, [74, 202,
    394, 458]), (5, [122, 218, 250, 378]), (6, [138, 266, 330]), (7, [378, 410, 474]), (8, [74, 234, 266]), (9, [251,
    299, 411])]⟩

set_option maxHeartbeats 0 in
theorem white_0011111101_check : white_0011111101.check = true := by decide +kernel

def white_00000011101 : WhiteRun := ⟨11, 0b00000011101,
  9, 44, [(0, [13, 25, 45, 97, 135, 153, 205, 333, 429]), (1, [21, 47, 101, 165, 179, 373, 457, 495]), (2, [33, 53, 97,
    127, 189, 277, 413, 443, 445]), (3, [85, 115, 129, 133, 137, 179, 229, 389, 437]), (4, [149, 157, 205, 213, 275,
    317, 413, 451, 461, 479]), (5, [65, 101, 117, 229, 341, 373, 445, 453, 485, 501]), (6, [21, 61, 109, 133, 149, 189,
    227, 277, 317, 341]), (7, [52, 68, 164, 308, 340, 388, 436, 452, 460, 500]), (8, [23, 87, 111, 119, 151, 207, 239,
    343, 447, 471]), (9, [48, 80, 128, 144, 160, 208, 288, 336, 368, 496]), (10, [24, 88, 124, 216, 280, 344, 432, 448,
    496, 504])]⟩

set_option maxHeartbeats 0 in
theorem white_00000011101_check : white_00000011101.check = true := by decide +kernel

def white_00001101011 : WhiteRun := ⟨11, 0b00001101011,
  10, 111, [(0, [429, 781]), (1, [259, 405, 677]), (2, [701, 757, 901]), (3, [205, 533, 645]), (4, [373, 717, 821]), (5,
    [468, 628, 788]), (6, [439, 599, 919]), (7, [241, 657, 977]), (8, [90, 282, 762]), (9, [203, 523, 939]), (10, [168,
    376, 792])]⟩

set_option maxHeartbeats 0 in
theorem white_00001101011_check : white_00001101011.check = true := by decide +kernel

def white_00001111111 : WhiteRun := ⟨11, 0b00001111111,
  9, 72, [(0, [26, 170, 194, 322]), (1, [43, 359, 427]), (2, [105, 169, 313]), (3, [175, 431, 463]), (4, [113, 123, 161,
    417]), (5, [136, 154, 178, 434]), (6, [158, 414, 477, 490]), (7, [42, 68, 226, 482]), (8, [54, 106, 239, 310]), (9,
    [82, 170, 288, 466]), (10, [94, 222, 426, 497])]⟩

set_option maxHeartbeats 0 in
theorem white_00001111111_check : white_00001111111.check = true := by decide +kernel

def white_00011111111 : WhiteRun := ⟨11, 0b00011111111,
  13, 161, [(0, [1002, 1514, 4074, 5250, 5354, 6250, 6338, 7338, 8170]), (1, [43, 1067, 1963, 3115, 3243, 3431, 4139,
    5931, 6087]), (2, [105, 2217, 3689, 4201, 4585, 5433, 5737, 6057, 6249]), (3, [175, 3247, 4271, 5039, 5583, 6319,
    6703, 7599]), (4, [416, 1184, 2912, 3488, 5232, 6048, 6560, 7328]), (5, [689, 1969, 3761, 4017, 4273, 5297, 5785,
    6449]), (6, [1690, 2202, 4058, 4250, 4762, 4846, 6042, 6554]), (7, [2794, 3818, 4170, 4330, 6634, 7658, 7714,
    7914]), (8, [554, 886, 1066, 3626, 4650, 6394, 6442, 6698]), (9, [1298, 1898, 2922, 3338, 3690, 4074, 4970, 8042]),
    (10, [298, 2346, 3518, 4138, 4190, 5034, 5530, 6442, 7466])]⟩

set_option maxHeartbeats 0 in
theorem white_00011111111_check : white_00011111111.check = true := by decide +kernel

def white_000000001011 : WhiteRun := ⟨12, 0b000000001011,
  12, 36, [(0, [62, 350, 502, 542, 614, 694, 766, 862, 958, 990, 1014, 1118, 1182, 1374, 1470, 1886, 1950, 2046, 2302,
    2494, 2526, 2878, 3038, 3134, 3230, 3422, 3678, 3934, 4094]), (1, [3, 67, 307, 323, 531, 835, 963, 1043, 1091, 1155,
    1347, 1451, 1539, 1603, 1683, 1795, 1827, 1859, 1979, 1987, 2019, 2051, 2115, 2275, 2371, 2499, 3203, 3331, 3395,
    3651, 3715, 3779, 4067]), (2, [5, 53, 229, 585, 613, 709, 869, 989, 997, 1125, 1277, 1381, 1413, 1853, 1989, 2101,
    2149, 2185, 2405, 2437, 2549, 2813, 2821, 3045, 3077, 3241, 3301, 3381, 3429, 3497, 3645, 3685, 3813, 3941, 4037]),
    (3, [13, 85, 109, 317, 573, 837, 957, 1085, 1093, 1199, 1341, 1493, 1549, 1645, 1853, 1903, 1967, 1981, 2047, 2109,
    2157, 2445, 2501, 2565, 3071, 3157, 3261, 3277, 3311, 3389, 3551, 3605, 3773, 3789, 3845, 3901]), (4, [21, 165, 213,
    397, 453, 629, 645, 821, 965, 1089, 1157, 1389, 1477, 1749, 1825, 1861, 1909, 1925, 2049, 2181, 2209, 2337, 2501,
    2829, 2837, 2981, 3141, 3157, 3237, 3525, 3653, 3693, 3797, 3821, 4001]), (5, [53, 179, 341, 445, 549, 597, 621,
    691, 725, 933, 1005, 1133, 1493, 1741, 1749, 1773, 1941, 1981, 2237, 2253, 2325, 2413, 2453, 2485, 2547, 2645, 3075,
    3181, 3349, 3365, 3507, 3533, 3693, 3811, 4045, 4083]), (6, [29, 85, 117, 413, 565, 645, 853, 933, 1061, 1141, 1181,
    1213, 1461, 1533, 1541, 1621, 1693, 1701, 1917, 1957, 2005, 2181, 2293, 2597, 2645, 2677, 3029, 3157, 3445, 3461,
    3613, 3733, 3749, 3829, 3877, 4021]), (7, [37, 149, 213, 229, 509, 533, 701, 741, 757, 805, 1213, 1229, 1301, 1365,
    1741, 1749, 1877, 2133, 2237, 2309, 2749, 2789, 2829, 2941, 2965, 3029, 3077, 3221, 3349, 3533, 3709, 3733, 3973,
    4069]), (8, [61, 125, 205, 317, 341, 501, 517, 757, 901, 1141, 1461, 1533, 1549, 1557, 1597, 1669, 1845, 2037, 2133,
    2293, 2309, 2389, 2453, 2621, 2645, 2677, 2693, 3285, 3413, 3461, 3509, 3957, 3973, 3981]), (9, [68, 132, 204, 212,
    276, 372, 532, 852, 964, 1172, 1228, 1364, 1556, 1804, 1876, 2068, 2516, 2764, 2836, 2868, 2884, 2964, 3028, 3076,
    3220, 3284, 3348, 3732, 3828, 3924, 3980]), (10, [214, 238, 278, 342, 374, 462, 534, 758, 790, 950, 1134, 1366,
    1462, 1550, 1846, 1878, 2038, 2134, 2294, 2390, 2414, 2454, 2486, 2518, 2678, 2870, 3126, 3414, 3670, 3902, 3958,
    4086]), (11, [18, 274, 290, 338, 450, 626, 786, 850, 946, 978, 1170, 1362, 1458, 1554, 1618, 1842, 2066, 2386, 2514,
    2834, 2962, 3218, 3282, 3346, 3410, 3666, 3730, 3746, 3826, 3874, 3922])]⟩

set_option maxHeartbeats 0 in
theorem white_000000001011_check : white_000000001011.check = true := by decide +kernel

def white_000000010001 : WhiteRun := ⟨12, 0b000000010001,
  12, 119, [(0, [68, 964, 1092, 2500, 3396, 3780]), (1, [238, 622, 1134, 1390, 3694, 3822]), (2, [291, 547, 931, 1909,
    1955, 3363, 3747]), (3, [693, 1013, 1205, 1525, 1909, 2229, 2325]), (4, [1045, 1685, 2325, 3093, 3477, 3989, 4021]),
    (5, [149, 245, 1269, 1589, 2805, 3637, 4021]), (6, [149, 277, 501, 853, 2581, 2901, 3861]), (7, [437, 501, 533, 949,
    1365, 2389, 2869]), (8, [532, 660, 1172, 1844, 2516, 3412, 3924]), (9, [342, 1366, 1782, 1846, 2518, 3670, 4086]),
    (10, [19, 851, 979, 2515, 2579, 3411, 3667]), (11, [61, 989, 1117, 1373, 2877, 3677])]⟩

set_option maxHeartbeats 0 in
theorem white_000000010001_check : white_000000010001.check = true := by decide +kernel

def white_000000011101 : WhiteRun := ⟨12, 0b000000011101,
  8, 52, [(0, [13, 77, 205]), (1, [21, 117, 245]), (2, [21, 53, 149]), (3, [53, 85, 245]), (4, [21, 85, 213]), (5, [53,
    85, 213]), (6, [85, 189, 213]), (7, [85, 133, 213]), (8, [84, 204, 212]), (9, [87, 119, 215]), (10, [80, 144, 208]),
    (11, [88, 216, 248])]⟩

set_option maxHeartbeats 0 in
theorem white_000000011101_check : white_000000011101.check = true := by decide +kernel

def white_000000110011 : WhiteRun := ⟨12, 0b000000110011,
  8, 67, [(0, [125, 253]), (1, [5, 133]), (2, [13, 205]), (3, [21, 117]), (4, [53, 149, 205]), (5, [85, 117, 245]), (6,
    [3, 21, 149, 213]), (7, [4, 52, 84, 244]), (8, [15, 23, 87, 215]), (9, [17, 49, 81, 209]), (10, [59, 91, 219]), (11,
    [72, 200])]⟩

set_option maxHeartbeats 0 in
theorem white_000000110011_check : white_000000110011.check = true := by decide +kernel

def white_000001001101 : WhiteRun := ⟨12, 0b000001001101,
  12, 302, [(0, [1326, 1566, 1838, 2350, 3374]), (1, [1507, 2531, 2851, 3555, 4067]), (2, [53, 1077, 2549, 3125, 3637]),
    (3, [85, 853, 1621, 3605, 3669]), (4, [213, 821, 981, 1365, 3029]), (5, [341, 1109, 1493, 2133, 3413]), (6, [852,
    1364, 3156, 3284, 3796]), (7, [598, 1366, 1750, 1878, 3414]), (8, [1363, 2003, 2387, 2643, 3411]), (9, [1372, 2140,
    3036, 3420, 3932]), (10, [327, 1351, 2055, 2119, 3271, 3399]), (11, [873, 1385, 1897, 3081, 3305, 3433])]⟩

set_option maxHeartbeats 0 in
theorem white_000001001101_check : white_000001001101.check = true := by decide +kernel

def white_000001101011 : WhiteRun := ⟨12, 0b000001101011,
  12, 125, [(0, [525, 1037, 1293, 2061, 3439, 3853]), (1, [405, 1313, 1813, 3093, 3477, 3605]), (2, [757, 821, 1269,
    1589, 2485, 3571]), (3, [1053, 1493, 1557, 2901, 3733, 3861]), (4, [437, 757, 2389, 2869, 3157, 3621]), (5, [661,
    893, 1557, 1749, 2517, 3925]), (6, [340, 1284, 1780, 2644, 2868, 3668]), (7, [855, 983, 2519, 2583, 3031, 3471]),
    (8, [1105, 1233, 1361, 2129, 2761, 2865, 3665]), (9, [986, 2522, 2686, 3290, 3418, 3802, 3930]), (10, [331, 587,
    1099, 1355, 1867, 2947, 3659]), (11, [888, 1016, 2040, 2244, 2424, 3448, 3832])]⟩

set_option maxHeartbeats 0 in
theorem white_000001101011_check : white_000001101011.check = true := by decide +kernel

def white_000010010001 : WhiteRun := ⟨12, 0b000010010001,
  10, 88, [(0, [110, 430]), (1, [163, 675]), (2, [437, 693]), (3, [661]), (4, [757]), (5, [532, 756]), (6, [534, 822]),
    (7, [467, 819]), (8, [476, 604]), (9, [582, 966]), (10, [107, 1003]), (11, [41, 169])]⟩

set_option maxHeartbeats 0 in
theorem white_000010010001_check : white_000010010001.check = true := by decide +kernel

def white_000011011011 : WhiteRun := ⟨12, 0b000011011011,
  12, 142, [(0, [1245, 1709, 2221, 2269, 3069]), (1, [659, 2053, 2725, 3397, 3493, 3909]), (2, [365, 1213, 1389, 1789,
    2749, 3085]), (3, [805, 1557, 2565, 2693, 3365, 3973]), (4, [205, 1533, 2765, 2829, 2869]), (5, [372, 2452, 2516,
    2676, 3076]), (6, [791, 1551, 2967, 3671, 3831]), (7, [529, 977, 1457, 2289, 2833]), (8, [1114, 1850, 2490, 3226,
    3354]), (9, [1450, 2026, 2506, 3722, 3786]), (10, [635, 731, 2091, 3243, 3707]), (11, [904, 1608, 1928, 1960,
    3176])]⟩

set_option maxHeartbeats 0 in
theorem white_000011011011_check : white_000011011011.check = true := by decide +kernel

def white_000011111111 : WhiteRun := ⟨12, 0b000011111111,
  7, 27, [(0, [10, 26, 42, 58, 102, 106]), (1, [27, 43, 59, 75, 107, 119]), (2, [17, 41, 73, 105, 121]), (3, [15, 47,
    59, 111, 127]), (4, [1, 17, 33, 41, 73, 97]), (5, [2, 50, 58, 110, 114, 126]), (6, [2, 6, 30, 34, 74, 94]), (7, [6,
    10, 34, 66, 118, 122]), (8, [1, 10, 18, 26, 102, 118]), (9, [2, 18, 26, 42, 58, 62]), (10, [6, 42, 62, 66, 74,
    106]), (11, [10, 42, 66, 102, 106, 122])]⟩

set_option maxHeartbeats 0 in
theorem white_000011111111_check : white_000011111111.check = true := by decide +kernel

def white_001011111011 : WhiteRun := ⟨12, 0b001011111011,
  7, 82, [(0, [13, 77]), (1, [21, 117]), (2, [21, 53]), (3, [52, 84]), (4, [86]), (5, [82]), (6, [94]), (7, [66]), (8,
    [94, 102]), (9, [58, 66]), (10, [75, 103]), (11, [56, 120])]⟩

set_option maxHeartbeats 0 in
theorem white_001011111011_check : white_001011111011.check = true := by decide +kernel

def white_001100111111 : WhiteRun := ⟨12, 0b001100111111,
  12, 120, [(0, [682, 1258, 1610, 2058, 2426, 3306, 3402]), (1, [1403, 1707, 1835, 3067, 3099, 3851, 3883]), (2, [409,
    489, 1577, 2057, 2537, 2729, 3337]), (3, [558, 750, 1438, 2734, 2926, 3102, 3630]), (4, [866, 1570, 1890, 2338,
    2722, 3298]), (5, [1335, 1847, 2359, 2743, 2935, 3003, 4087]), (6, [17, 2185, 2321, 2513, 2705, 3537, 4049]), (7,
    [58, 90, 1114, 2810, 3550, 3674, 4026]), (8, [74, 138, 202, 970, 1090, 2570, 3786]), (9, [250, 378, 474, 634, 1146,
    2842, 3814]), (10, [266, 570, 586, 778, 1930, 2474, 3722]), (11, [730, 922, 1434, 1866, 2042, 2266, 3754])]⟩

set_option maxHeartbeats 0 in
theorem white_001100111111_check : white_001100111111.check = true := by decide +kernel

def white_001111111101 : WhiteRun := ⟨12, 0b001111111101,
  7, 41, [(0, [24, 40, 72, 104]), (1, [44, 108, 124]), (2, [6, 38, 102]), (3, [10, 58, 122]), (4, [10, 26, 74]), (5,
    [26, 42, 122]), (6, [10, 42, 106]), (7, [26, 42, 106]), (8, [1, 42, 106]), (9, [2, 42, 106]), (10, [6, 42, 106]),
    (11, [11, 43, 107])]⟩

set_option maxHeartbeats 0 in
theorem white_001111111101_check : white_001111111101.check = true := by decide +kernel

def white_011101111111 : WhiteRun := ⟨12, 0b011101111111,
  7, 72, [(0, [26, 42, 58, 122]), (1, [11, 43, 75, 107]), (2, [24, 40, 104, 120]), (3, [13, 45, 109]), (4, [20, 36,
    100]), (5, [54, 62, 126]), (6, [2, 66, 82]), (7, [6, 94, 102]), (8, [10, 58, 66]), (9, [26, 74, 94, 102]), (10, [42,
    58, 66, 122]), (11, [10, 74, 102, 106])]⟩

set_option maxHeartbeats 0 in
theorem white_011101111111_check : white_011101111111.check = true := by decide +kernel

end LockBlocks

/-- **An entry whose check passes**: once the center column repeats its block from time `T`, read from phase `shift`,
column `width + 1` is black at some time in every stretch of `len` steps from `T` on. -/
theorem center_white_run (e : WhiteRun) (hc : e.check = true) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.period e.bits).getD ((t + shift) % e.period) false) (t0 : Nat)
    (ht0 : T ≤ t0) : ∃ i, i < e.len ∧ Rule30Jen.cell (t0 + i) ((e.width : Int) + 1) = true := by
  obtain ⟨i, hi, hne⟩ := center_lockBlock _ e.width 0 e.len e.groups 300 hc T shift
    (fun t ht => by rw [h t ht, Rule30StripCertificateTable.wordOf_length]) t0 ht0
  rw [Nat.zero_testBit] at hne
  exact ⟨i, hi, by simpa using hne⟩

/-- The 22 blocks whose shortest steering white run over the widths 4 to 16 comes at a width of at most 13, each at
that width. -/
def whiteRuns : List WhiteRun := [
    white_00000101, white_00111101, white_00111111, white_0001111111, white_0011111101, white_00000011101,
    white_00001101011, white_00001111111, white_00011111111, white_000000001011, white_000000010001, white_000000011101,
    white_000000110011, white_000001001101, white_000001101011, white_000010010001, white_000011011011,
    white_000011111111, white_001011111011, white_001100111111, white_001111111101, white_011101111111]

/-- Every check passes. -/
theorem whiteRuns_check : ∀ e ∈ whiteRuns, e.check = true := by
  intro e he
  simp only [whiteRuns, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact white_00000101_check
  · exact white_00111101_check
  · exact white_00111111_check
  · exact white_0001111111_check
  · exact white_0011111101_check
  · exact white_00000011101_check
  · exact white_00001101011_check
  · exact white_00001111111_check
  · exact white_00011111111_check
  · exact white_000000001011_check
  · exact white_000000010001_check
  · exact white_000000011101_check
  · exact white_000000110011_check
  · exact white_000001001101_check
  · exact white_000001101011_check
  · exact white_000010010001_check
  · exact white_000011011011_check
  · exact white_000011111111_check
  · exact white_001011111011_check
  · exact white_001100111111_check
  · exact white_001111111101_check
  · exact white_011101111111_check

/-- **The 22 blocks**: once the center column repeats the block of an entry of `whiteRuns` from time `T`, read from
phase `shift`, column `width + 1` is black at some time in every stretch of `len` steps from `T` on. -/
theorem center_white_runs (e : WhiteRun) (he : e ∈ whiteRuns) (T shift : Nat)
    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t =
      (Rule30StripCertificateTable.wordOf e.period e.bits).getD ((t + shift) % e.period) false) (t0 : Nat)
    (ht0 : T ≤ t0) : ∃ i, i < e.len ∧ Rule30Jen.cell (t0 + i) ((e.width : Int) + 1) = true :=
  center_white_run e (whiteRuns_check e he) T shift h t0 ht0

/-- **The sufficient condition**: if column `width + 1` has `len` white cells in a row at arbitrarily late times, the
center column does not eventually repeat the block of the entry. -/
theorem not_eventually_white_runs (e : WhiteRun) (he : e ∈ whiteRuns)
    (hw : ∀ N, ∃ t0, N ≤ t0 ∧ ∀ i, i < e.len → Rule30Jen.cell (t0 + i) ((e.width : Int) + 1) = false) :
    ¬ Rule30StripCertificates.EventuallyWord (Rule30StripCertificateTable.wordOf e.period e.bits) := by
  have hc := whiteRuns_check e he
  have hP : 0 < e.period := by
    have hc' := hc
    unfold WhiteRun.check lockCheckB at hc'
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc'
    have h1 := hc'.1.1.1.1.2
    rwa [Rule30StripCertificateTable.wordOf_length] at h1
  rintro ⟨T, hT⟩
  obtain ⟨t0, ht0, hr⟩ := hw T
  obtain ⟨i, hi, hb⟩ := center_white_run e hc T (e.period * T - T) (fun t ht => by
    rw [← evolve_single_center, evolve_single_eq_cell]
    show Rule30Jen.cell t 0 = _
    have hLT : T ≤ e.period * T := Nat.le_mul_of_pos_left T hP
    rw [hT t ht, Rule30StripCertificateTable.wordOf_length,
      show t + (e.period * T - T) = t - T + e.period * T by omega, Nat.add_mul_mod_self_left]) t0 ht0
  rw [hr i hi] at hb
  exact Bool.false_ne_true hb

end Rule30Open
