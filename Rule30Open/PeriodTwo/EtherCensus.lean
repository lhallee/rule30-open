module

public import Rule30Open.PeriodTwo.ShiftModel
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers
public import Ruliology.CellularAutomata.Rule30Ether

/-!
# Every head of up to 12 cells on the ether settles

The ether is the cycle of four states of the held map on a ring of seven cells (`eth`, a cycle of the rule on the
whole line by `eth_step`; it is the kit's `Rule30Ether.ether` read from right to left, `eth_eq_kit_ether`). Lay it on
the cells `j ≥ 0` at an alignment `(a, o)`, phase `a` and offset `o`, and compare a half `u` with it: the defect
`defect u a o t j` is cell `j` of `heldOrbit u t` xor `eth (a + t) (j + o)`. It follows a rule of its own
(`defect_succ`, `defect_succ_zero`), and its top rises by at most one cell per step (`defect_clear_succ`).

* **Closed strips.** `closedTab` holds 1,915 strips of 13 cells, 433, 533, 344 and 605 at the four phases
  (`closed_count`), at the cells `c` with `(c + o) mod 7 = 5`. The kernel checks that each steps to a strip of the
  set at the next phase for both values of the cell below it, and that the cell above it stays clear
  (`closedOK_true`, `closed_facts`). So a defect that is clear above `c` with its strip at `c` in the set stays so
  forever, whatever lies below (`stripInv_forever`).
* **The census.** `runHead` follows the defect of one head as a number (`Enc`, stepped exactly by `dstep` while it
  stays below cell 126, `enc_step`), in rounds of four steps, until it lies in a closed strip or repeats a snapshot
  taken at the steps `4 · 2^k`; every step must keep it below cell 61. It is sound (`runHead_sound`), and the kernel
  runs it on all 2^12 heads at each of the 28 alignments in chunks of 1,024 (`census`).
* **The theorems.** If the cells of `u` from `p ≤ 12` on are the ether at an alignment, every cell from 61 on is the
  ether at every step (`ether_tail_clear`); the orbit of `u` is then eventually periodic
  (`ether_tail_eventually_periodic`, through `eventually_periodic_of_clear`: a defect below a fixed cell takes finitely
  many values), and so is its itinerary (`ether_tail_itinerary`). This is conjecture (R) of the shift model for the
  2-adic rationals whose tail from cell 12 on is the ether, whether or not they are in `InK`.

The natural-language argument is `EtherCensus.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

/-! ### The ether -/

/-- The four states of the ether on a ring of seven cells, bit `j` the ring cell `j`. -/
def etherWord (a : Nat) : Nat := [64, 97, 19, 126].getD (a % 4) 0

/-- Cell `j` of ether state `a`, both read modulo the cycle. -/
def eth (a j : Nat) : Bool := (etherWord a).testBit (j % 7)

theorem eth_congr {a a' j j' : Nat} (ha : a % 4 = a' % 4) (hj : j % 7 = j' % 7) : eth a j = eth a' j' := by
  unfold eth etherWord; rw [ha, hj]

theorem eth_step_small : ∀ a, a < 4 → ∀ j, j < 7 →
    eth (a + 1) j = xor (eth a (j + 1)) (eth a j || eth a (j + 6)) := by decide

/-- **The ether is a cycle of the held rule on the whole line**: cell `j` at phase `a + 1` is cell `j + 1` xor
(cell `j` or cell `j - 1`) at phase `a`, with `j - 1` read as `j + 6`. -/
theorem eth_step (a j : Nat) : eth (a + 1) j = xor (eth a (j + 1)) (eth a j || eth a (j + 6)) := by
  have h := eth_step_small (a % 4) (Nat.mod_lt _ (by decide)) (j % 7) (Nat.mod_lt _ (by decide))
  rw [eth_congr (a := a + 1) (a' := a % 4 + 1) (j := j) (j' := j % 7) (by omega) (by omega),
    eth_congr (a := a) (a' := a % 4) (j := j + 1) (j' := j % 7 + 1) (by omega) (by omega),
    eth_congr (a := a) (a' := a % 4) (j := j + 6) (j' := j % 7 + 6) (by omega) (by omega),
    eth_congr (a := a) (a' := a % 4) (j := j) (j' := j % 7) (by omega) (by omega)]
  exact h

/-- **The ether is the kit's**: `eth a j` is the kit's ether column `1 - j` (modulo 7) at phase `a`, read from right to
left since bit `j` of the held map is the cell `j + 1` places left of the column. -/
theorem eth_eq_kit_ether (a j : Nat) : eth a j = Ruliology.CellularAutomata.Rule30Ether.ether (6 * j + 1) a := by
  have h : ∀ a, a < 4 → ∀ j, j < 7 → eth a j = Ruliology.CellularAutomata.Rule30Ether.ether (6 * j + 1) a := by
    decide
  rw [eth_congr (a' := a % 4) (j' := j % 7) (by omega) (by omega), h _ (Nat.mod_lt _ (by decide)) _
    (Nat.mod_lt _ (by decide))]
  exact Ruliology.CellularAutomata.Rule30Ether.ether_congr (by omega) (by omega)

/-! ### The defect against the ether -/

/-- The defect of `u` against the ether at alignment `(a, o)`: cell `j` of `heldOrbit u t` xor the ether cell
`eth (a + t) (j + o)`. -/
def defect (u : Nat → Bool) (a o t j : Nat) : Bool := xor (heldOrbit u t j) (eth (a + t) (j + o))

/-- The defect rule at one cell, from the defect `dm d dp` at the cells `j - 1, j, j + 1` and the background `bm b` at
the cells `j - 1, j`. -/
def dcell (dm d dp bm b : Bool) : Bool := xor dp (xor (xor d b || xor dm bm) (b || bm))

private theorem dcell_alg (x0 x1 x2 e0 e1 e2 : Bool) :
    xor (xor x2 (x1 || x0)) (xor e2 (e1 || e0)) = dcell (xor x0 e0) (xor x1 e1) (xor x2 e2) e0 e1 := by
  revert x0 x1 x2 e0 e1 e2; decide

private theorem dcell_alg0 (x0 x1 e0 e1 e6 : Bool) :
    xor (xor x1 x0) (xor e1 (e0 || e6)) = dcell e6 (xor x0 e0) (xor x1 e1) e6 e0 := by
  revert x0 x1 e0 e1 e6; decide

theorem dcell_zero (bm b : Bool) : dcell false false false bm b = false := by
  revert bm b; decide

theorem defect_succ (u : Nat → Bool) (a o t j : Nat) :
    defect u a o (t + 1) (j + 1) = dcell (defect u a o t j) (defect u a o t (j + 1)) (defect u a o t (j + 2))
      (eth (a + t) (j + o)) (eth (a + t) (j + 1 + o)) := by
  unfold defect
  show xor (xor (heldOrbit u t (j + 2)) (heldOrbit u t (j + 1) || heldOrbit u t j)) (eth (a + (t + 1)) (j + 1 + o)) = _
  rw [show a + (t + 1) = a + t + 1 by omega, eth_step,
    eth_congr (a' := a + t) (j' := j + o) rfl (show (j + 1 + o + 6) % 7 = (j + o) % 7 by omega),
    show j + 1 + o + 1 = j + 2 + o by omega]
  exact dcell_alg _ _ _ _ _ _

theorem defect_succ_zero (u : Nat → Bool) (a o t : Nat) :
    defect u a o (t + 1) 0 = dcell (eth (a + t) (o + 6)) (defect u a o t 0) (defect u a o t 1)
      (eth (a + t) (o + 6)) (eth (a + t) o) := by
  unfold defect
  show xor (xor (heldOrbit u t 1) (heldOrbit u t 0)) (eth (a + (t + 1)) (0 + o)) = _
  rw [show a + (t + 1) = a + t + 1 by omega, eth_step, Nat.zero_add, show o + 1 = 1 + o by omega]
  exact dcell_alg0 _ _ _ _ _

/-- **The top rises by at most one cell per step**: a defect that is clear from cell `W` on is clear from cell
`W + 1` on one step later. -/
theorem defect_clear_succ (u : Nat → Bool) (a o t W : Nat) (h : ∀ j, W ≤ j → defect u a o t j = false) :
    ∀ j, W + 1 ≤ j → defect u a o (t + 1) j = false := by
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [defect_succ, h i (by omega), h (i + 1) (by omega), h (i + 2) (by omega)]
  exact dcell_zero _ _

theorem heldOrbit_eq_defect (u : Nat → Bool) (a o t j : Nat) :
    heldOrbit u t j = xor (defect u a o t j) (eth (a + t) (j + o)) := by
  unfold defect; cases heldOrbit u t j <;> cases eth (a + t) (j + o) <;> rfl

/-- `f s` for every `s < n`. -/
def allBelow (f : Nat → Bool) (n : Nat) : Bool := Nat.rec (motive := fun _ => Bool) true (fun k ih => f k && ih) n

theorem allBelow_spec (f : Nat → Bool) : ∀ n, allBelow f n = true → ∀ s, s < n → f s = true := by
  intro n
  induction n with
  | zero => intro _ s hs; omega
  | succ n ih =>
    intro h s hs
    have h' : f n = true ∧ allBelow f n = true := Bool.and_eq_true_iff.mp h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact ih h'.2 s hs
    · exact h'.1

/-! ### The defect as a number -/

/-- `n` holds the defect at step `t`, bit `j` the cell `j`. -/
def Enc (u : Nat → Bool) (a o t n : Nat) : Prop := ∀ j, defect u a o t j = n.testBit j

/-- The ether cells `0 .. 127` at the 28 alignments, entry `7 a + o` for phase `a` and offset `o`. -/
def bgTab : List Nat := [42870219454606420593810974164632215616, 21435109727303210296905487082316107808, 10717554863651605148452743541158053904, 5358777431825802574226371770579026952, 2679388715912901287113185885289513476, 171480877818425682375243896658528862466, 85740438909212841187621948329264431233, 150045768091122472078338409576212754657, 75022884045561236039169204788106377328, 37511442022780618019584602394053188664, 18755721011390309009792301197026594332, 179519043966164386236583454314397402894, 259900705443551424849979030873082807175, 300091536182244944156676819152425509315, 267938871591290128711318588528951347603, 133969435795645064355659294264475673801, 66984717897822532177829647132237836900, 203633542409380497820602127282003024178, 101816771204690248910301063641001512089, 50908385602345124455150531820500756044, 195595376261641793959262569626134483750, 254541928011725622275752659102503780222, 297412147466332042869563633267135995839, 318847257193635253166469120349452103647, 329564812057286858314921863890610157551, 334923589489112660889148235661189184503, 337602978205025562176261421546478697979, 168801489102512781088130710773239348989]

/-- The background cells `0 .. 127` at phase `a` and offset `o`. -/
def bgL (a o : Nat) : Nat := bgTab.getD (7 * (a % 4) + o % 7) 0

/-- The check that `bgTab` holds the ether. -/
def bgCheck : Bool :=
  allBelow (fun a => allBelow (fun o => allBelow (fun j => (bgL a o).testBit j == eth a (j + o)) 128) 7) 4

theorem bgCheck_true : bgCheck = true := by decide +kernel

theorem bgL_small (a o j : Nat) (ha : a < 4) (ho : o < 7) (hj : j < 128) : (bgL a o).testBit j = eth a (j + o) :=
  beq_iff_eq.mp (allBelow_spec _ _ (allBelow_spec _ _ (allBelow_spec _ _ bgCheck_true a ha) o ho) j hj)

theorem bgL_testBit (a o j : Nat) (hj : j < 128) : (bgL a o).testBit j = eth a (j + o) := by
  have h := bgL_small (a % 4) (o % 7) j (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hj
  rw [show bgL (a % 4) (o % 7) = bgL a o by unfold bgL; rw [Nat.mod_mod, Nat.mod_mod]] at h
  rw [h]; exact eth_congr (by omega) (by omega)

theorem bgL_mod (a o : Nat) : bgL (a % 4) o = bgL a o := by unfold bgL; rw [Nat.mod_mod]

/-- One step of the defect `n` with the background `b` before and `b'` after, kept to the cells `0 .. 126`. Written
with the raw operations, which the kernel evaluates on numbers. -/
def dstep (b b' n : Nat) : Nat :=
  Nat.mod (Nat.xor (Nat.xor (Nat.shiftRight (Nat.xor n b) 1) (Nat.lor (Nat.xor n b) (Nat.shiftLeft (Nat.xor n b) 1)))
    b') 170141183460469231731687303715884105728

theorem dstep_eq (b b' n : Nat) : dstep b b' n = (heldNat (n ^^^ b) ^^^ b') % 2 ^ 127 := rfl

private theorem xor_xor_cancel (x e : Bool) : xor (xor x e) e = x := by cases x <;> cases e <;> rfl

theorem clear_of_enc {u : Nat → Bool} {a o t n L : Nat} (h : Enc u a o t n) (hn : n < 2 ^ L) :
    ∀ j, L ≤ j → defect u a o t j = false := by
  intro j hj
  rw [h j]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hj))

/-- **The step on numbers is exact** while the top of the defect is below cell 126. -/
theorem enc_step {u : Nat → Bool} {a o t n : Nat} (h : Enc u a o t n) (hn : n < 2 ^ 126) :
    Enc u a o (t + 1) (dstep (bgL (a + t) o) (bgL (a + t + 1) o) n) := by
  intro j
  rw [dstep_eq, Nat.testBit_mod_two_pow]
  by_cases hj : j < 127
  · have hx : ∀ i, i < 128 → (n ^^^ bgL (a + t) o).testBit i = heldOrbit u t i := by
      intro i hi
      rw [Nat.testBit_xor, ← h i, bgL_testBit _ _ _ hi, heldOrbit_eq_defect u a o t i]
    rw [decide_eq_true hj, Bool.true_and, Nat.testBit_xor, heldNat_testBit, bgL_testBit _ _ _ (by omega)]
    unfold defect
    rw [show a + (t + 1) = a + t + 1 by omega]
    congr 1
    show held (heldOrbit u t) j = held (fun i => (n ^^^ bgL (a + t) o).testBit i) j
    cases j with
    | zero =>
      show xor (heldOrbit u t 1) (heldOrbit u t 0) =
        xor ((n ^^^ bgL (a + t) o).testBit 1) ((n ^^^ bgL (a + t) o).testBit 0)
      rw [hx 1 (by omega), hx 0 (by omega)]
    | succ j =>
      show xor (heldOrbit u t (j + 2)) (heldOrbit u t (j + 1) || heldOrbit u t j) =
        xor ((n ^^^ bgL (a + t) o).testBit (j + 2))
          ((n ^^^ bgL (a + t) o).testBit (j + 1) || (n ^^^ bgL (a + t) o).testBit j)
      rw [hx (j + 2) (by omega), hx (j + 1) (by omega), hx j (by omega)]
  · rw [decide_eq_false hj, Bool.false_and]
    exact defect_clear_succ u a o t 126 (clear_of_enc h hn) j (by omega)

/-! ### Closed strips -/

/-- The strip of 13 cells `c - 12 .. c` of `D`, bit `i` the cell `c - 12 + i`. -/
def stripOf (D : Nat → Bool) (c : Nat) : Nat := natOf (fun i => D (c - 12 + i)) 13

theorem stripOf_testBit (D : Nat → Bool) (c i : Nat) :
    (stripOf D c).testBit i = (decide (i < 13) && D (c - 12 + i)) :=
  natOf_testBit 13 _ i

theorem natOf_lt (u : Nat → Bool) (N : Nat) : natOf u N < 2 ^ N :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by rw [natOf_testBit, decide_eq_false (by omega), Bool.false_and]

/-- The closed strips at the four phases, at the cells `c` with `(c + o) mod 7 = 5`: entry `a` is a number whose bit
`s` is the strip `s`. -/
def closedTab : List Nat := [
  21345086845432781220653130188827197089566045482325682452617721700475700660554445906456851716327614853093001986166083345878532923651707718760964741830343288796810773163792171488626770791166791199644046870541140326546454604664479798071705215496398204923711652410200359352000777307003029399592963362738373288194496468634678170825953606615672899975882673546632077753377175533559689230661054843187494327529575899298344894712574208259252964619516941080471236143958050918318458859756846188685320014236011387335775503376097051430296390639536703005541509186105965244401352908387592016539500961953806689975311168472176740808827296604901595073629030576360740537006064876503650585291395257684030435482184820223459811439455906655836161597021505295574510803973152296830998386375789819638778036328677244435975727132894028438075924421645667745930190272360165249774285650947769908064684299548280968305899288371323164895010939160134781869512519800131766183992661687206295191213841691904328069393390191272021945192259099612070924465324564938442551662357141782078468291797886404639108814479046142626957982151790251256088115836608130093364797513025113962083059116520032685580816037307275318702335468370023545044443288699831483698652386412750042464878542457435541737092120361015775602593784266395583985927370293547987282949869167373301246116510362605325247703545258059718138064779771529119091090440533073050349737562424811140765437758383791774169619700613860660661147700649433845230890264876637558462320821723323781477716090395630639191553004495962112,
  734841070477003395029862653740810281428875891512234265523994953912674082913689178774659214093650695206894728664656311527469140576362016695053207181754417900482830240036097253649547291330586812061179361565747600586444994572013580518797836088039566779541371915434305960283699125722953586904911995185441684370629585264009036204339265955942296600950478338362884561887598847024723490810125254259360479547846571910763760859480746277078409208921705596290564877013056640278560007935390464117687079509201727711285024863882801408172791235195187723315097470993442084885534194454197756163911331196429186537571372443792130905310199850278824104197988146041814090745764930206748595686504605494651744696162265157930664302126903895921317091521871007751252059233241877887526776685469599115315282800139870769701521272607727281605305087737446659733832756876946842183455338360394222662096594816267859999020527020758028829582998536211114087343204928554400727153607637917286658103079144092919751108393102289143510587029017549823024719197849447633156312675079108701545200350095441949204086270535368184014212944415161811273700759587634061527090437849664976704358954716482088728588888718215816006353176828320363595907918922614031366021736254128047133815698537403359857997310762710358291471466007639885406376042005764777405823339194278552028916074925624548074150063615702330947213140652055532771194178497102938627801719106765048625423239914667882350339793764697318893345891389406911804009084949997478976233850682739112906267237599413926331517765197818625739968292179688611041056737548040473075548342657550132087748730607710406971966893030957554694888693257521242276686010441689439574730845739704506394336950493689529335841483218311826387408298593781590809595628135875592543594408757045116946912668614632543133558346572260865200616074573364964541331744283487835006329578880530278923119466204192487916543441660170317098838076742302318399680376957277014316715666077162769142677545868162368219811898842993820631211839571410567504960290317236848566167512510880553929907524964284122718088229198303680086812335937050306377540667695667085295442209870847009512327499371493397868426172541276286984112201734096746785851972494040606127933779211061252825625102284306578826200610198836669592596254097533114089126090174773928853306838757703512505058530938744490637201884558546328081794155214530204042222607944200711300900314577834626683584495398553178651754496,
  1848588718335577800360581457423581388868410986225686425566856403840759335350787283474195705604176988345812651263904191984076459206251354976560588306638745423234715926783812413623926719569874310141672371267412229741524518884204472071685108052911106904735611767785833926801698226659298501993190050614276830062008690385361222702406063221905529035582420388612180566591060307426255220361188807101736691219961889550301765187017972069866793212499657040671205875291752824286924052046238471884650950019218253818638349581503822874626557508414698682479374647565120179298928858237880351768993752751486154581806644416147632040164618242627916289986819588863179820030931362861404420393664572315497399904535519907127199180497973351713499379463150448589899177517693872406160525403241607164883370203033407449451881077066455880479586799911842857587180973698802693616339729071937612464663719272366807344887596246874827140119802898265616290713070250761521368547791034521619593403593579021694606937229386175500002434621555768462499924581065795698146578322472178524311134713899709934407263813634303645711547911052709376521294724225922450980919584178318137390531234773988905174002015940920639684798453693796806881189772066827427838715427755050226688196608,
  1967053152596237647903479252007730968687324084763440455941461785653577396922312042875617552813343991228326671139941659469043818946340588986436373411015861068518306800312623436025672916288036506708347025620045999214892272289001290519360802298669471754675663031592346574982371472242551315834084528035626649677823353654315423459480981068962669915624974841301704590054417409853332182233806165973895665176585851905731097090996488621956125463042777207577560100808572432715253881983987954476075774180723404063687802593612142781296365599125113197694469423033093450383638596845305565312031208391698639076018783183797298675265939676998073998237465491006836822650138945650954934678609976093076790669804734176694849215406564345004224956790528879164201907575669472648963461755810207557375352504753217103511320323440910750753371090208377610986025931598052515242805003221620206200423546819933877670377308223841761387487915621713644920111091846892921920505443089795545057945958719352981817697236304862253032967761696336849975188806241968583214946519501168027978981901603157157361361736792594108604860766527514497887454525755694705436738657477687334056317850059494131446921643311538439988058512264407401133560360369189271180643762157891332243193189759285854801580220265829771755530010634349092899338919108106318904892771138108129517179218547745962184055764952836095787332204953308281525614310393250571941455088852471186377756742290281262386480075155219918153925240284651094286594839657649485866766288209016666637754338970827123601299398431293754550710060968434250172107099443304722708289262685497388428470096052743832813537653225757922162823545179459073370171307545627292371471911533115771774664590581977204191320219606237117890151795834529428236348459432848108056499674328410179966484440092507275809054148635898616582133207764500252389028683985142498740830533199188699370473066292532267869248265131067812901322486441955911684113292410210977800542874646194052557939331201986380776841741480086295573406076757597978719518228221026530955478465483578321489116575678023532964507238740740525849917723144457660600152797702395830192429692210774540912205115241321966606716437528857202222369590436339575638253086225565217673362851027323449251688860000336984585977353545635649804283780950958412221689665004282723591878419018806341804730354148577661364400367334939956911701969249293918822659801777326006529858153684764127940933527431589085260398134354614076376669532580396505828896502854975488]

/-- The closed strips at phase `a`. -/
def closedSet (a : Nat) : Nat := closedTab.getD (a % 4) 0

/-- Whether the strip `s` is closed at phase `a` and residue `r` of `c + o` modulo 7. -/
def closedMem (a r s : Nat) : Bool := Nat.beq (r % 7) 5 && (closedSet a).testBit s

/-- Cell `i` of the strip `s` one step later, at phase `a` and residue `r`, with the cell `b` below it; `i = 13` is
the cell above the strip. The background of the cell `c - 12 + i` is `eth a (r + 2 + i)`. -/
def newCell (a r s : Nat) (b : Bool) (i : Nat) : Bool :=
  dcell (if i = 0 then b else s.testBit (i - 1)) (s.testBit i) (s.testBit (i + 1)) (eth a (r + 1 + i))
    (eth a (r + 2 + i))

/-- The new cells of the strip `s` with the cell `b` below it, as one number: bit `i + 1` is `newCell a r s b i`
when `w` is the background `bgL a (r + 1)` (`stripRaw_testBit`). -/
def stripRaw (w s : Nat) (b : Bool) : Nat :=
  ((s <<< 1 ||| b.toNat) >>> 1) ^^^
    ((((s <<< 1 ||| b.toNat) ^^^ w) ||| (((s <<< 1 ||| b.toNat) ^^^ w) <<< 1)) ^^^ (w ||| (w <<< 1)))

/-- The strip `s` one step later. -/
def stripStep (a r s : Nat) (b : Bool) : Nat := (stripRaw (bgL a (r + 1)) s b >>> 1) % 8192

/-- Whether the cell above the strip `s` becomes a defect. -/
def stripRise (a r s : Nat) (b : Bool) : Bool := (stripRaw (bgL a (r + 1)) s b).testBit 14

private theorem zbit (s : Nat) (b : Bool) (k : Nat) :
    (s <<< 1 ||| b.toNat).testBit k = if k = 0 then b else s.testBit (k - 1) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_bool_toNat]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]; omega

theorem stripRaw_testBit (a r s : Nat) (b : Bool) (i : Nat) (hi : i ≤ 13) :
    (stripRaw (bgL a (r + 1)) s b).testBit (i + 1) = newCell a r s b i := by
  unfold stripRaw newCell dcell
  have hz := zbit s b
  have hw1 := bgL_testBit a (r + 1) (i + 1) (by omega)
  have hw0 := bgL_testBit a (r + 1) i (by omega)
  generalize s <<< 1 ||| b.toNat = z at hz ⊢
  generalize bgL a (r + 1) = w at hw1 hw0 ⊢
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, hz,
    show 1 + (i + 1) = i + 2 by omega, show i + 1 - 1 = i by omega, decide_eq_true (show i + 1 ≥ 1 by omega),
    Bool.true_and, ite_eq_right (show i + 1 ≠ 0 by omega), ite_eq_right (show i + 2 ≠ 0 by omega),
    show i + 2 - 1 = i + 1 by omega,
    hw1, hw0, show i + 1 + (r + 1) = r + 2 + i by omega, show i + (r + 1) = r + 1 + i by omega]


theorem stripStep_testBit (a r s : Nat) (b : Bool) (i : Nat) :
    (stripStep a r s b).testBit i = (decide (i < 13) && newCell a r s b i) := by
  unfold stripStep
  rw [show (8192 : Nat) = 2 ^ 13 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < 13
  · rw [show 1 + i = i + 1 by omega, stripRaw_testBit a r s b i (by omega)]
  · simp [hi]

theorem stripRise_eq (a r s : Nat) (b : Bool) : stripRise a r s b = newCell a r s b 13 :=
  stripRaw_testBit a r s b 13 (by omega)

/-- **The closure check**: at each phase `a`, every closed strip steps to a closed strip at phase `a + 1` for both
values of the cell below it, and the cell above it stays clear. -/
def closedOK : Bool :=
  allBelow (fun a => allBelow (fun s => !(closedSet a).testBit s ||
    ((closedSet (a + 1)).testBit (stripStep a 5 s false) && !stripRise a 5 s false &&
      (closedSet (a + 1)).testBit (stripStep a 5 s true) && !stripRise a 5 s true)) 8192) 4

theorem closedOK_true : closedOK = true := by decide +kernel

/-- The number of set bits of `x` below bit `n`. -/
def countBits (x n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih + (x.testBit k).toNat) n

set_option exponentiation.threshold 8192 in
/-- **There are 1,915 closed strips**: 433, 533, 344 and 605 at the four phases. -/
theorem closed_count : (List.range 4).map (fun a => countBits (closedSet a) 8192) = [433, 533, 344, 605] ∧
    ∀ a, a < 4 → closedSet a < 2 ^ 8192 := by
  decide +kernel

theorem closedSet_mod (a : Nat) : closedSet (a % 4) = closedSet a := by unfold closedSet; rw [Nat.mod_mod]

theorem newCell_mod (a r s : Nat) (b : Bool) (i : Nat) : newCell a r s b i = newCell (a % 4) (r % 7) s b i := by
  unfold newCell
  rw [eth_congr (a := a) (a' := a % 4) (j := r + 1 + i) (j' := r % 7 + 1 + i) (by omega) (by omega),
    eth_congr (a := a) (a' := a % 4) (j := r + 2 + i) (j' := r % 7 + 2 + i) (by omega) (by omega)]

theorem stripStep_mod (a r s : Nat) (b : Bool) : stripStep a r s b = stripStep (a % 4) (r % 7) s b :=
  Nat.eq_of_testBit_eq fun i => by rw [stripStep_testBit, stripStep_testBit, newCell_mod]

set_option exponentiation.threshold 8192 in
/-- **The closed strips are closed**: a closed strip steps to a closed strip and its top does not rise. -/
theorem closed_facts {a r s : Nat} (b : Bool) (h : closedMem a r s = true) :
    closedMem (a + 1) r (stripStep a r s b) = true ∧ newCell a r s b 13 = false := by
  unfold closedMem at h ⊢
  obtain ⟨hr, hs⟩ := Bool.and_eq_true_iff.mp h
  have hr5 : r % 7 = 5 := Nat.eq_of_beq_eq_true hr
  have ha : a % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcs : closedSet (a % 4) = closedSet a := closedSet_mod a
  have hlt : s < 8192 := by
    refine Nat.lt_of_not_le fun hge => ?_
    have hb := closed_count.2 (a % 4) ha
    rw [hcs] at hb
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hge))] at hs
    exact Bool.false_ne_true hs
  have hc := allBelow_spec _ _ (allBelow_spec _ _ closedOK_true (a % 4) ha) s hlt
  rw [hcs, hs, Bool.not_true, Bool.false_or] at hc
  have e1 : closedSet (a % 4 + 1) = closedSet (a + 1) := by
    rw [← closedSet_mod (a % 4 + 1), ← closedSet_mod (a + 1), show (a % 4 + 1) % 4 = (a + 1) % 4 by omega]
  have e2 : stripStep a r s b = stripStep (a % 4) 5 s b := by rw [stripStep_mod, hr5]
  have e3 : newCell a r s b 13 = stripRise (a % 4) 5 s b := by rw [stripRise_eq, newCell_mod, hr5]
  rw [e1] at hc
  rw [hr, Bool.true_and, e2, e3]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  cases b
  · exact ⟨hc.1.1.1, hc.1.1.2⟩
  · exact ⟨hc.1.2, hc.2⟩

/-! ### A defect in a closed strip stays below it -/

/-- The defect at step `t` is clear above cell `c` and its strip at `c` is closed. -/
def StripInv (u : Nat → Bool) (a o t c : Nat) : Prop :=
  (∀ j, c < j → defect u a o t j = false) ∧ closedMem (a + t) (c + o) (stripOf (defect u a o t) c) = true

/-- The defect one step later, cell by cell over the strip and the cell above it. -/
theorem strip_cell {u : Nat → Bool} {a o t c : Nat} (hc : 12 ≤ c) (hz : ∀ j, c < j → defect u a o t j = false)
    (i : Nat) (hi : i ≤ 13) :
    defect u a o (t + 1) (c - 12 + i) =
      newCell (a + t) (c + o) (stripOf (defect u a o t) c)
        (if c = 12 then eth (a + t) (o + 6) else defect u a o t (c - 13)) i := by
  have sb : ∀ k, (stripOf (defect u a o t) c).testBit k = (decide (k < 13) && defect u a o t (c - 12 + k)) :=
    stripOf_testBit _ c
  unfold newCell
  by_cases h0 : c - 12 + i = 0
  · have hc12 : c = 12 := by omega
    have hi0 : i = 0 := by omega
    subst hi0
    rw [h0, defect_succ_zero, ite_eq_left hc12, ite_eq_left rfl, sb 0, sb 1, hc12]
    simp only [decide_eq_true (show 0 < 13 by omega), decide_eq_true (show 1 < 13 by omega),
      Bool.true_and, show 12 - 12 + 0 = 0 by omega, show 12 - 12 + 1 = 1 by omega]
    rw [eth_congr (a := a + t) (a' := a + t) (j := 12 + o + 1) (j' := o + 6) rfl (by omega),
      eth_congr (a := a + t) (a' := a + t) (j := 12 + o + 2) (j' := o) rfl (by omega)]
  · obtain ⟨j, hj⟩ : ∃ j, c - 12 + i = j + 1 := ⟨c - 12 + i - 1, by omega⟩
    rw [hj, defect_succ]
    have hdm : (if i = 0 then (if c = 12 then eth (a + t) (o + 6) else defect u a o t (c - 13))
        else (stripOf (defect u a o t) c).testBit (i - 1)) = defect u a o t j := by
      by_cases hi0 : i = 0
      · rw [ite_eq_left hi0, ite_eq_right (by omega), show c - 13 = j by omega]
      · rw [ite_eq_right hi0, sb, decide_eq_true (by omega), Bool.true_and, show c - 12 + (i - 1) = j by omega]
    have hd : (stripOf (defect u a o t) c).testBit i = defect u a o t (j + 1) := by
      rw [sb]
      by_cases h13 : i < 13
      · rw [decide_eq_true h13, Bool.true_and, hj]
      · rw [decide_eq_false h13, Bool.false_and, hz (j + 1) (by omega)]
    have hdp : (stripOf (defect u a o t) c).testBit (i + 1) = defect u a o t (j + 2) := by
      rw [sb]
      by_cases h13 : i + 1 < 13
      · rw [decide_eq_true h13, Bool.true_and, show c - 12 + (i + 1) = j + 2 by omega]
      · rw [decide_eq_false h13, Bool.false_and, hz (j + 2) (by omega)]
    rw [hdm, hd, hdp,
      eth_congr (a := a + t) (a' := a + t) (j := c + o + 1 + i) (j' := j + o) rfl (by omega),
      eth_congr (a := a + t) (a' := a + t) (j := c + o + 2 + i) (j' := j + 1 + o) rfl (by omega)]

/-- **A closed strip keeps the defect below it for one step.** -/
theorem stripInv_step {u : Nat → Bool} {a o t c : Nat} (hc : 12 ≤ c) (h : StripInv u a o t c) :
    StripInv u a o (t + 1) c := by
  obtain ⟨hz, hm⟩ := h
  let b := if c = 12 then eth (a + t) (o + 6) else defect u a o t (c - 13)
  have facts := closed_facts b hm
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases hj1 : j = c + 1
    · subst hj1
      rw [show c + 1 = c - 12 + 13 by omega, strip_cell hc hz 13 (by omega)]
      exact facts.2
    · exact defect_clear_succ u a o t (c + 1) (fun k hk => hz k (by omega)) j (by omega)
  · have e : stripOf (defect u a o (t + 1)) c = stripStep (a + t) (c + o) (stripOf (defect u a o t) c) b := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [stripOf_testBit, stripStep_testBit]
      by_cases hi : i < 13
      · rw [decide_eq_true hi, Bool.true_and, Bool.true_and, strip_cell hc hz i (by omega)]
      · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]
    rw [e, show a + (t + 1) = a + t + 1 by omega]
    exact facts.1

/-- **A defect in a closed strip stays below it forever.** -/
theorem stripInv_forever {u : Nat → Bool} {a o t c : Nat} (hc : 12 ≤ c) (h : StripInv u a o t c) :
    ∀ m, StripInv u a o (t + m) c := by
  intro m
  induction m with
  | zero => exact h
  | succ m ih => exact stripInv_step hc ih

/-! ### The census checker -/

/-- `k v`, with `v` evaluated once by the kernel before it is passed on. -/
def letN (v : Nat) (k : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (k 0) (fun m _ => k (Nat.succ m)) v

theorem letN_eq (v : Nat) (k : Nat → Bool) : letN v k = k v := by cases v <;> rfl

/-- The least cell `c` among `c0, c0 + 7, …` (at most `k` tries) with the defect `n` clear above `c`. -/
def firstAbove (n k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun _ ih c => cond (Nat.beq (Nat.shiftRight n (Nat.add c 1)) 0) c (ih (Nat.add c 7))) k

/-- Whether the defect `n` lies in a closed strip of `cl` at the cell `c`, with `12 ≤ c < L`. -/
def cand (cl o L n c : Nat) : Bool :=
  Nat.blt c L && Nat.ble 12 c && Nat.beq (Nat.mod (Nat.add c o) 7) 5 && Nat.beq (Nat.shiftRight n (Nat.add c 1)) 0 &&
    Nat.testBit cl (Nat.mod (Nat.shiftRight n (Nat.sub c 12)) 8192)

/-- Whether the defect `n` lies in a closed strip at one of the three least cells `c ≥ max(top, 12)` with
`(c + o) mod 7 = 5`. -/
def closedAt (cl o L n : Nat) : Bool :=
  letN (firstAbove n 20 (Nat.add 12 (Nat.mod (Nat.sub 12 (Nat.mod (Nat.add 12 o) 7)) 7))) fun c =>
    cand cl o L n c || cand cl o L n (Nat.add c 7) || cand cl o L n (Nat.add c 14)

/-- The checker of one head at offset `o`, in rounds of four steps from a step `t` that is a multiple of 4: the
backgrounds `b0 … b3` of the four phases, the closed strips `cl` of the first phase, the bound `L` on the cells of the
defect `n`, a snapshot `snap` taken at step `snapT`, and the step `nxt` of the next snapshot. A round succeeds when
the defect lies in a closed strip or equals the snapshot; otherwise it takes four steps, each of which must leave the
defect below cell `L`. -/
def runHead (o L b0 b1 b2 b3 cl : Nat) (fuel : Nat) : Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ _ _ _ _ => false)
    (fun _ ih t n snap snapT nxt =>
      closedAt cl o L n || (Nat.blt snapT t && Nat.beq n snap) ||
      letN (dstep b0 b1 n) fun n1 => Nat.beq (Nat.shiftRight n1 L) 0 &&
      letN (dstep b1 b2 n1) fun n2 => Nat.beq (Nat.shiftRight n2 L) 0 &&
      letN (dstep b2 b3 n2) fun n3 => Nat.beq (Nat.shiftRight n3 L) 0 &&
      letN (dstep b3 b0 n3) fun n4 => Nat.beq (Nat.shiftRight n4 L) 0 &&
      cond (Nat.beq t nxt) (ih (Nat.add t 4) n4 n t (Nat.mul 2 t)) (ih (Nat.add t 4) n4 snap snapT nxt))
    fuel

theorem cand_sound {cl o L n c : Nat} (h : cand cl o L n c = true) :
    c < L ∧ 12 ≤ c ∧ (c + o) % 7 = 5 ∧ n >>> (c + 1) = 0 ∧ cl.testBit ((n >>> (c - 12)) % 8192) = true := by
  unfold cand at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, h5⟩

theorem closedAt_sound {cl o L n : Nat} (h : closedAt cl o L n = true) : ∃ c, cand cl o L n c = true := by
  unfold closedAt at h
  rw [letN_eq] at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

theorem bgL_phase {x y : Nat} (o : Nat) (h : x % 4 = y % 4) : bgL x o = bgL y o := by
  rw [← bgL_mod x, ← bgL_mod y, h]

theorem closedSet_phase {x y : Nat} (h : x % 4 = y % 4) : closedSet x = closedSet y := by
  rw [← closedSet_mod x, ← closedSet_mod y, h]

theorem lt_of_shiftRight_eq_zero {n L : Nat} (h : n >>> L = 0) : n < 2 ^ L := by
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos L)).mp h

/-- A defect in a closed strip found by the checker. -/
theorem stripInv_of_cand {u : Nat → Bool} {a o t n L c : Nat} (he : Enc u a o t n) (ht : t % 4 = 0)
    (h : cand (closedSet a) o L n c = true) : StripInv u a o t c ∧ c < L ∧ 12 ≤ c := by
  obtain ⟨hcL, hc12, hr, hz, hm⟩ := cand_sound h
  refine ⟨⟨fun j hj => ?_, ?_⟩, hcL, hc12⟩
  · rw [he j, show j = (c + 1) + (j - (c + 1)) by omega, ← Nat.testBit_shiftRight, hz, Nat.zero_testBit]
  · have e : stripOf (defect u a o t) c = (n >>> (c - 12)) % 8192 := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [stripOf_testBit, show (8192 : Nat) = 2 ^ 13 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, he]
    unfold closedMem
    rw [e, closedSet_phase (show (a + t) % 4 = a % 4 by omega), hm, Bool.and_true]
    exact Nat.beq_eq_true_eq _ _ ▸ hr

/-- Two steps with the same defect and the same phase have the same row. -/
theorem heldOrbit_eq_of_enc {u : Nat → Bool} {a o t1 t2 n : Nat} (h1 : Enc u a o t1 n) (h2 : Enc u a o t2 n)
    (h : t1 % 4 = t2 % 4) : heldOrbit u t1 = heldOrbit u t2 := by
  funext j
  rw [heldOrbit_eq_defect u a o t1 j, heldOrbit_eq_defect u a o t2 j, h1 j, h2 j,
    eth_congr (a := a + t1) (a' := a + t2) (j := j + o) (j' := j + o) (by omega) rfl]

theorem heldOrbit_repeat {u : Nat → Bool} {i P : Nat} (h : heldOrbit u (i + P) = heldOrbit u i) :
    ∀ q r, heldOrbit u (i + P * q + r) = heldOrbit u (i + r) := by
  have hq : ∀ q, heldOrbit u (i + P * q) = heldOrbit u i := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [show i + P * (q + 1) = (i + P) + P * q by rw [Nat.mul_succ]; omega, ← heldOrbit_add, h, heldOrbit_add, ih]
  intro q r
  rw [← heldOrbit_add, hq, heldOrbit_add]

/-- A defect whose row repeats after `P` steps, `P` a multiple of 4, is clear from cell `L` on at every step if it is
at the steps up to the repeat. -/
theorem clear_of_repeat {u : Nat → Bool} {a o i P L : Nat} (hP : 0 < P) (h4 : P % 4 = 0)
    (h : heldOrbit u (i + P) = heldOrbit u i) (hb : ∀ k j, k ≤ i + P → L ≤ j → defect u a o k j = false) :
    ∀ k j, L ≤ j → defect u a o k j = false := by
  intro k j hj
  by_cases hk : k ≤ i + P
  · exact hb k j hk hj
  · have e := heldOrbit_repeat h ((k - i) / P) ((k - i) % P)
    rw [show i + P * ((k - i) / P) + (k - i) % P = k by
      have := Nat.div_add_mod (k - i) P; omega] at e
    have hm := hb (i + (k - i) % P) j (by have := Nat.mod_lt (k - i) hP; omega) hj
    unfold defect at hm ⊢
    rw [e, eth_congr (a := a + k) (a' := a + (i + (k - i) % P)) (j := j + o) (j' := j + o) ?_ rfl]
    · exact hm
    · have := Nat.div_add_mod (k - i) P
      have h4' : P * ((k - i) / P) % 4 = 0 := by rw [Nat.mul_mod, h4, Nat.zero_mul, Nat.zero_mod]
      omega

/-- **The checker is sound**: a head that `runHead` settles has its defect clear from cell `L` on at every step. -/
theorem runHead_sound (u : Nat → Bool) (a o L : Nat) (hL : L ≤ 126) :
    ∀ fuel t n snap snapT nxt,
      runHead o L (bgL a o) (bgL (a + 1) o) (bgL (a + 2) o) (bgL (a + 3) o) (closedSet a) fuel t n snap snapT nxt
        = true →
      t % 4 = 0 → snapT % 4 = 0 → snapT ≤ t → Enc u a o t n → Enc u a o snapT snap →
      (∀ k j, k ≤ t → L ≤ j → defect u a o k j = false) →
      ∀ k j, L ≤ j → defect u a o k j = false := by
  intro fuel
  induction fuel with
  | zero => intro t n snap snapT nxt h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro t n snap snapT nxt h ht hs hst he hse hb
    have hn : n < 2 ^ L :=
      Nat.lt_pow_two_of_testBit _ fun j hj => by rw [← he j]; exact hb t j (Nat.le_refl t) hj
    have h126 : ∀ m, m < 2 ^ L → m < 2 ^ 126 :=
      fun m hm => Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hL)
    have h' := h
    simp only [runHead] at h'
    rw [letN_eq, letN_eq, letN_eq, letN_eq] at h'
    rw [Bool.or_eq_true, Bool.or_eq_true] at h'
    rcases h' with (hc | hrep) | hsteps
    · -- a closed strip
      obtain ⟨c, hcand⟩ := closedAt_sound hc
      obtain ⟨hinv, hcL, hc12⟩ := stripInv_of_cand he ht hcand
      intro k j hj
      by_cases hk : k ≤ t
      · exact hb k j hk hj
      · have := (stripInv_forever hc12 hinv (k - t)).1 j (by omega)
        rwa [show t + (k - t) = k by omega] at this
    · -- a repeat of the snapshot
      rw [Bool.and_eq_true] at hrep
      have hlt' : snapT < t := Nat.le_of_ble_eq_true hrep.1
      have hnn : n = snap := Nat.eq_of_beq_eq_true hrep.2
      subst hnn
      have hrow := heldOrbit_eq_of_enc he hse (by omega)
      refine clear_of_repeat (i := snapT) (P := t - snapT) (by omega) (by omega) ?_ ?_
      · rw [show snapT + (t - snapT) = t by omega]; exact hrow
      · intro k j hk hj; exact hb k j (by omega) hj
    · -- four steps
      simp only [Bool.and_eq_true] at hsteps
      obtain ⟨h1, h2, h3, h4, hrest⟩ := hsteps
      have e1 : Enc u a o (t + 1) (dstep (bgL a o) (bgL (a + 1) o) n) := by
        have := enc_step he (h126 n hn)
        rwa [bgL_phase o (show (a + t) % 4 = a % 4 by omega),
          bgL_phase o (show (a + t + 1) % 4 = (a + 1) % 4 by omega)] at this
      generalize dstep (bgL a o) (bgL (a + 1) o) n = n1 at e1 h1 h2 h3 h4 hrest
      have l1 : n1 < 2 ^ L := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h1)
      have e2 : Enc u a o (t + 2) (dstep (bgL (a + 1) o) (bgL (a + 2) o) n1) := by
        have := enc_step e1 (h126 n1 l1)
        rwa [bgL_phase o (show (a + (t + 1)) % 4 = (a + 1) % 4 by omega),
          bgL_phase o (show (a + (t + 1) + 1) % 4 = (a + 2) % 4 by omega)] at this
      generalize dstep (bgL (a + 1) o) (bgL (a + 2) o) n1 = n2 at e2 h2 h3 h4 hrest
      have l2 : n2 < 2 ^ L := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h2)
      have e3 : Enc u a o (t + 3) (dstep (bgL (a + 2) o) (bgL (a + 3) o) n2) := by
        have := enc_step e2 (h126 n2 l2)
        rwa [bgL_phase o (show (a + (t + 2)) % 4 = (a + 2) % 4 by omega),
          bgL_phase o (show (a + (t + 2) + 1) % 4 = (a + 3) % 4 by omega)] at this
      generalize dstep (bgL (a + 2) o) (bgL (a + 3) o) n2 = n3 at e3 h3 h4 hrest
      have l3 : n3 < 2 ^ L := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h3)
      have e4 : Enc u a o (t + 4) (dstep (bgL (a + 3) o) (bgL a o) n3) := by
        have := enc_step e3 (h126 n3 l3)
        rwa [bgL_phase o (show (a + (t + 3)) % 4 = (a + 3) % 4 by omega),
          bgL_phase o (show (a + (t + 3) + 1) % 4 = a % 4 by omega)] at this
      generalize dstep (bgL (a + 3) o) (bgL a o) n3 = n4 at e4 h4 hrest
      have l4 : n4 < 2 ^ L := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h4)
      have hb4 : ∀ k j, k ≤ t + 4 → L ≤ j → defect u a o k j = false := by
        intro k j hk hj
        by_cases hkt : k ≤ t
        · exact hb k j hkt hj
        · rcases (show k = t + 1 ∨ k = t + 2 ∨ k = t + 3 ∨ k = t + 4 by omega) with rfl | rfl | rfl | rfl
          · exact clear_of_enc e1 l1 j hj
          · exact clear_of_enc e2 l2 j hj
          · exact clear_of_enc e3 l3 j hj
          · exact clear_of_enc e4 l4 j hj
      cases hnx : Nat.beq t nxt
      · rw [hnx] at hrest
        exact ih (t + 4) n4 snap snapT (nxt) hrest (by omega) hs (by omega) e4 hse hb4
      · rw [hnx] at hrest
        exact ih (t + 4) n4 n t (2 * t) hrest (by omega) ht (by omega) e4 he hb4

/-! ### The census in chunks -/

/-- Every head `h` with `lo ≤ h < hi` at the alignment `(a, o)` passes the checker with the bound `L` and `fuel`
rounds. -/
def HeadsOK (a o L fuel lo hi : Nat) : Prop :=
  ∀ h, lo ≤ h → h < hi →
    runHead o L (bgL a o) (bgL (a + 1) o) (bgL (a + 2) o) (bgL (a + 3) o) (closedSet a) fuel 0 h h 0 4 = true

/-- The heads `lo, …, lo + cnt - 1` at the alignment `(a, o)`, as one kernel computation. -/
def chunkOK (a o L fuel lo cnt : Nat) : Bool :=
  allBelow (fun k => runHead o L (bgL a o) (bgL (a + 1) o) (bgL (a + 2) o) (bgL (a + 3) o) (closedSet a) fuel 0
    (lo + k) (lo + k) 0 4) cnt

theorem headsOK_of_chunk {a o L fuel lo cnt : Nat} (h : chunkOK a o L fuel lo cnt = true) :
    HeadsOK a o L fuel lo (lo + cnt) := by
  intro x hlo hhi
  have := allBelow_spec _ cnt h (x - lo) (by omega)
  rwa [show lo + (x - lo) = x by omega] at this

theorem headsOK_append {a o L fuel lo mid hi : Nat} (h1 : HeadsOK a o L fuel lo mid) (h2 : HeadsOK a o L fuel mid hi) :
    HeadsOK a o L fuel lo hi := by
  intro x hlo hhi
  by_cases hx : x < mid
  · exact h1 x hlo hx
  · exact h2 x (by omega) hhi

/-- A census at one alignment bounds the defect of every half whose tail from cell `p` on is the ether there. -/
theorem clear_of_census {u : Nat → Bool} {a o p L fuel : Nat} (hL : L ≤ 126) (hpL : p ≤ L)
    (hH : HeadsOK a o L fuel 0 (2 ^ p)) (hu : ∀ j, p ≤ j → u j = eth a (j + o)) :
    ∀ k j, L ≤ j → defect u a o k j = false := by
  have hd : ∀ j, p ≤ j → defect u a o 0 j = false := by
    intro j hj
    unfold defect
    rw [show heldOrbit u 0 j = u j from rfl, hu j hj, Nat.add_zero]
    cases eth a (j + o) <;> rfl
  have he : Enc u a o 0 (natOf (defect u a o 0) p) := by
    intro j
    rw [natOf_testBit]
    by_cases hj : j < p
    · rw [decide_eq_true hj, Bool.true_and]
    · rw [decide_eq_false hj, Bool.false_and, hd j (by omega)]
  refine runHead_sound u a o L hL fuel 0 _ _ 0 4 (hH _ (Nat.zero_le _) (natOf_lt _ p)) rfl rfl (Nat.le_refl 0) he he ?_
  intro k j hk hj
  rw [show k = 0 by omega]
  exact hd j (by omega)

/-! ### A bounded defect gives an eventually periodic orbit -/

/-- **A bounded defect means an eventually periodic orbit**: the defect clear from cell `L` on at every step takes
finitely many values, so the row repeats at two steps of the same phase. -/
theorem eventually_periodic_of_clear {u : Nat → Bool} {a o L : Nat}
    (h : ∀ k j, L ≤ j → defect u a o k j = false) :
    ∃ T P, 0 < P ∧ ∀ t, T ≤ t → heldOrbit u (t + P) = heldOrbit u t := by
  let f : Nat → Nat := fun t => natOf (defect u a o t) L * 4 + t % 4
  have hf : ∀ t, f t ∈ List.range (2 ^ L * 4) := by
    intro t
    rw [List.mem_range]
    have := natOf_lt (defect u a o t) L
    have := Nat.mod_lt t (show 0 < 4 by decide)
    show natOf (defect u a o t) L * 4 + t % 4 < 2 ^ L * 4
    omega
  obtain ⟨m, n, hmn, -, hfe⟩ :=
    Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers.pigeonhole_gen (List.range (2 ^ L * 4)) f hf
  have h4 : m % 4 = n % 4 := by
    have := Nat.mod_lt m (show 0 < 4 by decide)
    have := Nat.mod_lt n (show 0 < 4 by decide)
    show m % 4 = n % 4
    simp only [f] at hfe
    omega
  have hN : natOf (defect u a o m) L = natOf (defect u a o n) L := by
    simp only [f] at hfe
    omega
  have hrow : heldOrbit u m = heldOrbit u n := by
    funext j
    have hd : defect u a o m j = defect u a o n j := by
      by_cases hj : j < L
      · have h1 := natOf_testBit L (defect u a o m) j
        have h2 := natOf_testBit L (defect u a o n) j
        rw [hN, decide_eq_true hj, Bool.true_and] at h1
        rw [decide_eq_true hj, Bool.true_and] at h2
        rw [← h1, h2]
      · rw [h m j (by omega), h n j (by omega)]
    rw [heldOrbit_eq_defect u a o m j, heldOrbit_eq_defect u a o n j, hd,
      eth_congr (a := a + m) (a' := a + n) (j := j + o) (j' := j + o) (by omega) rfl]
  refine ⟨m, n - m, by omega, fun t ht => ?_⟩
  rw [show t + (n - m) = n + (t - m) by omega, ← heldOrbit_add, ← hrow, heldOrbit_add,
    show m + (t - m) = t by omega]

/-- An eventually periodic orbit has an eventually periodic itinerary. -/
theorem itinerary_of_eventually_periodic {u : Nat → Bool} {T P : Nat} (hP : 0 < P)
    (h : ∀ t, T ≤ t → heldOrbit u (t + P) = heldOrbit u t) :
    ∃ pre n, 0 < n ∧ ∀ s, pre ≤ s → itinerary u (s + n) = itinerary u s := by
  refine ⟨T, P, hP, fun s hs => ?_⟩
  show heldOrbit u (2 * (s + P)) 0 = heldOrbit u (2 * s) 0
  rw [show 2 * (s + P) = 2 * s + P + P by omega, h (2 * s + P) (by omega), h (2 * s) (by omega)]

/-! ### The census -/

theorem census_0_0_0 : chunkOK 0 0 61 80 0 1024 = true := by
  decide +kernel

theorem census_0_0_1 : chunkOK 0 0 61 80 1024 1024 = true := by
  decide +kernel

theorem census_0_0_2 : chunkOK 0 0 61 80 2048 1024 = true := by
  decide +kernel

theorem census_0_0_3 : chunkOK 0 0 61 80 3072 1024 = true := by
  decide +kernel

theorem census_0_1_0 : chunkOK 0 1 61 80 0 1024 = true := by
  decide +kernel

theorem census_0_1_1 : chunkOK 0 1 61 80 1024 1024 = true := by
  decide +kernel

theorem census_0_1_2 : chunkOK 0 1 61 80 2048 1024 = true := by
  decide +kernel

theorem census_0_1_3 : chunkOK 0 1 61 80 3072 1024 = true := by
  decide +kernel

theorem census_0_2_0 : chunkOK 0 2 61 80 0 1024 = true := by
  decide +kernel

theorem census_0_2_1 : chunkOK 0 2 61 80 1024 1024 = true := by
  decide +kernel

theorem census_0_2_2 : chunkOK 0 2 61 80 2048 1024 = true := by
  decide +kernel

theorem census_0_2_3 : chunkOK 0 2 61 80 3072 1024 = true := by
  decide +kernel

theorem census_0_3_0 : chunkOK 0 3 61 80 0 1024 = true := by
  decide +kernel

theorem census_0_3_1 : chunkOK 0 3 61 80 1024 1024 = true := by
  decide +kernel

theorem census_0_3_2 : chunkOK 0 3 61 80 2048 1024 = true := by
  decide +kernel

theorem census_0_3_3 : chunkOK 0 3 61 80 3072 1024 = true := by
  decide +kernel

theorem census_0_4_0 : chunkOK 0 4 61 80 0 1024 = true := by
  decide +kernel

theorem census_0_4_1 : chunkOK 0 4 61 80 1024 1024 = true := by
  decide +kernel

theorem census_0_4_2 : chunkOK 0 4 61 80 2048 1024 = true := by
  decide +kernel

theorem census_0_4_3 : chunkOK 0 4 61 80 3072 1024 = true := by
  decide +kernel

theorem census_0_5_0 : chunkOK 0 5 61 80 0 1024 = true := by
  decide +kernel

theorem census_0_5_1 : chunkOK 0 5 61 80 1024 1024 = true := by
  decide +kernel

theorem census_0_5_2 : chunkOK 0 5 61 80 2048 1024 = true := by
  decide +kernel

theorem census_0_5_3 : chunkOK 0 5 61 80 3072 1024 = true := by
  decide +kernel

theorem census_0_6_0 : chunkOK 0 6 61 80 0 1024 = true := by
  decide +kernel

theorem census_0_6_1 : chunkOK 0 6 61 80 1024 1024 = true := by
  decide +kernel

theorem census_0_6_2 : chunkOK 0 6 61 80 2048 1024 = true := by
  decide +kernel

theorem census_0_6_3 : chunkOK 0 6 61 80 3072 1024 = true := by
  decide +kernel

theorem census_1_0_0 : chunkOK 1 0 61 80 0 1024 = true := by
  decide +kernel

theorem census_1_0_1 : chunkOK 1 0 61 80 1024 1024 = true := by
  decide +kernel

theorem census_1_0_2 : chunkOK 1 0 61 80 2048 1024 = true := by
  decide +kernel

theorem census_1_0_3 : chunkOK 1 0 61 80 3072 1024 = true := by
  decide +kernel

theorem census_1_1_0 : chunkOK 1 1 61 80 0 1024 = true := by
  decide +kernel

theorem census_1_1_1 : chunkOK 1 1 61 80 1024 1024 = true := by
  decide +kernel

theorem census_1_1_2 : chunkOK 1 1 61 80 2048 1024 = true := by
  decide +kernel

theorem census_1_1_3 : chunkOK 1 1 61 80 3072 1024 = true := by
  decide +kernel

theorem census_1_2_0 : chunkOK 1 2 61 80 0 1024 = true := by
  decide +kernel

theorem census_1_2_1 : chunkOK 1 2 61 80 1024 1024 = true := by
  decide +kernel

theorem census_1_2_2 : chunkOK 1 2 61 80 2048 1024 = true := by
  decide +kernel

theorem census_1_2_3 : chunkOK 1 2 61 80 3072 1024 = true := by
  decide +kernel

theorem census_1_3_0 : chunkOK 1 3 61 80 0 1024 = true := by
  decide +kernel

theorem census_1_3_1 : chunkOK 1 3 61 80 1024 1024 = true := by
  decide +kernel

theorem census_1_3_2 : chunkOK 1 3 61 80 2048 1024 = true := by
  decide +kernel

theorem census_1_3_3 : chunkOK 1 3 61 80 3072 1024 = true := by
  decide +kernel

theorem census_1_4_0 : chunkOK 1 4 61 80 0 1024 = true := by
  decide +kernel

theorem census_1_4_1 : chunkOK 1 4 61 80 1024 1024 = true := by
  decide +kernel

theorem census_1_4_2 : chunkOK 1 4 61 80 2048 1024 = true := by
  decide +kernel

theorem census_1_4_3 : chunkOK 1 4 61 80 3072 1024 = true := by
  decide +kernel

theorem census_1_5_0 : chunkOK 1 5 61 80 0 1024 = true := by
  decide +kernel

theorem census_1_5_1 : chunkOK 1 5 61 80 1024 1024 = true := by
  decide +kernel

theorem census_1_5_2 : chunkOK 1 5 61 80 2048 1024 = true := by
  decide +kernel

theorem census_1_5_3 : chunkOK 1 5 61 80 3072 1024 = true := by
  decide +kernel

theorem census_1_6_0 : chunkOK 1 6 61 80 0 1024 = true := by
  decide +kernel

theorem census_1_6_1 : chunkOK 1 6 61 80 1024 1024 = true := by
  decide +kernel

theorem census_1_6_2 : chunkOK 1 6 61 80 2048 1024 = true := by
  decide +kernel

theorem census_1_6_3 : chunkOK 1 6 61 80 3072 1024 = true := by
  decide +kernel

theorem census_2_0_0 : chunkOK 2 0 61 80 0 1024 = true := by
  decide +kernel

theorem census_2_0_1 : chunkOK 2 0 61 80 1024 1024 = true := by
  decide +kernel

theorem census_2_0_2 : chunkOK 2 0 61 80 2048 1024 = true := by
  decide +kernel

theorem census_2_0_3 : chunkOK 2 0 61 80 3072 1024 = true := by
  decide +kernel

theorem census_2_1_0 : chunkOK 2 1 61 80 0 1024 = true := by
  decide +kernel

theorem census_2_1_1 : chunkOK 2 1 61 80 1024 1024 = true := by
  decide +kernel

theorem census_2_1_2 : chunkOK 2 1 61 80 2048 1024 = true := by
  decide +kernel

theorem census_2_1_3 : chunkOK 2 1 61 80 3072 1024 = true := by
  decide +kernel

theorem census_2_2_0 : chunkOK 2 2 61 80 0 1024 = true := by
  decide +kernel

theorem census_2_2_1 : chunkOK 2 2 61 80 1024 1024 = true := by
  decide +kernel

theorem census_2_2_2 : chunkOK 2 2 61 80 2048 1024 = true := by
  decide +kernel

theorem census_2_2_3 : chunkOK 2 2 61 80 3072 1024 = true := by
  decide +kernel

theorem census_2_3_0 : chunkOK 2 3 61 80 0 1024 = true := by
  decide +kernel

theorem census_2_3_1 : chunkOK 2 3 61 80 1024 1024 = true := by
  decide +kernel

theorem census_2_3_2 : chunkOK 2 3 61 80 2048 1024 = true := by
  decide +kernel

theorem census_2_3_3 : chunkOK 2 3 61 80 3072 1024 = true := by
  decide +kernel

theorem census_2_4_0 : chunkOK 2 4 61 80 0 1024 = true := by
  decide +kernel

theorem census_2_4_1 : chunkOK 2 4 61 80 1024 1024 = true := by
  decide +kernel

theorem census_2_4_2 : chunkOK 2 4 61 80 2048 1024 = true := by
  decide +kernel

theorem census_2_4_3 : chunkOK 2 4 61 80 3072 1024 = true := by
  decide +kernel

theorem census_2_5_0 : chunkOK 2 5 61 80 0 1024 = true := by
  decide +kernel

theorem census_2_5_1 : chunkOK 2 5 61 80 1024 1024 = true := by
  decide +kernel

theorem census_2_5_2 : chunkOK 2 5 61 80 2048 1024 = true := by
  decide +kernel

theorem census_2_5_3 : chunkOK 2 5 61 80 3072 1024 = true := by
  decide +kernel

theorem census_2_6_0 : chunkOK 2 6 61 80 0 1024 = true := by
  decide +kernel

theorem census_2_6_1 : chunkOK 2 6 61 80 1024 1024 = true := by
  decide +kernel

theorem census_2_6_2 : chunkOK 2 6 61 80 2048 1024 = true := by
  decide +kernel

theorem census_2_6_3 : chunkOK 2 6 61 80 3072 1024 = true := by
  decide +kernel

theorem census_3_0_0 : chunkOK 3 0 61 80 0 1024 = true := by
  decide +kernel

theorem census_3_0_1 : chunkOK 3 0 61 80 1024 1024 = true := by
  decide +kernel

theorem census_3_0_2 : chunkOK 3 0 61 80 2048 1024 = true := by
  decide +kernel

theorem census_3_0_3 : chunkOK 3 0 61 80 3072 1024 = true := by
  decide +kernel

theorem census_3_1_0 : chunkOK 3 1 61 80 0 1024 = true := by
  decide +kernel

theorem census_3_1_1 : chunkOK 3 1 61 80 1024 1024 = true := by
  decide +kernel

theorem census_3_1_2 : chunkOK 3 1 61 80 2048 1024 = true := by
  decide +kernel

theorem census_3_1_3 : chunkOK 3 1 61 80 3072 1024 = true := by
  decide +kernel

theorem census_3_2_0 : chunkOK 3 2 61 80 0 1024 = true := by
  decide +kernel

theorem census_3_2_1 : chunkOK 3 2 61 80 1024 1024 = true := by
  decide +kernel

theorem census_3_2_2 : chunkOK 3 2 61 80 2048 1024 = true := by
  decide +kernel

theorem census_3_2_3 : chunkOK 3 2 61 80 3072 1024 = true := by
  decide +kernel

theorem census_3_3_0 : chunkOK 3 3 61 80 0 1024 = true := by
  decide +kernel

theorem census_3_3_1 : chunkOK 3 3 61 80 1024 1024 = true := by
  decide +kernel

theorem census_3_3_2 : chunkOK 3 3 61 80 2048 1024 = true := by
  decide +kernel

theorem census_3_3_3 : chunkOK 3 3 61 80 3072 1024 = true := by
  decide +kernel

theorem census_3_4_0 : chunkOK 3 4 61 80 0 1024 = true := by
  decide +kernel

theorem census_3_4_1 : chunkOK 3 4 61 80 1024 1024 = true := by
  decide +kernel

theorem census_3_4_2 : chunkOK 3 4 61 80 2048 1024 = true := by
  decide +kernel

theorem census_3_4_3 : chunkOK 3 4 61 80 3072 1024 = true := by
  decide +kernel

theorem census_3_5_0 : chunkOK 3 5 61 80 0 1024 = true := by
  decide +kernel

theorem census_3_5_1 : chunkOK 3 5 61 80 1024 1024 = true := by
  decide +kernel

theorem census_3_5_2 : chunkOK 3 5 61 80 2048 1024 = true := by
  decide +kernel

theorem census_3_5_3 : chunkOK 3 5 61 80 3072 1024 = true := by
  decide +kernel

theorem census_3_6_0 : chunkOK 3 6 61 80 0 1024 = true := by
  decide +kernel

theorem census_3_6_1 : chunkOK 3 6 61 80 1024 1024 = true := by
  decide +kernel

theorem census_3_6_2 : chunkOK 3 6 61 80 2048 1024 = true := by
  decide +kernel

theorem census_3_6_3 : chunkOK 3 6 61 80 3072 1024 = true := by
  decide +kernel

theorem census_0_0 : HeadsOK 0 0 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_0_0_0) (headsOK_of_chunk census_0_0_1)) (headsOK_of_chunk census_0_0_2)) (headsOK_of_chunk census_0_0_3)

theorem census_0_1 : HeadsOK 0 1 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_0_1_0) (headsOK_of_chunk census_0_1_1)) (headsOK_of_chunk census_0_1_2)) (headsOK_of_chunk census_0_1_3)

theorem census_0_2 : HeadsOK 0 2 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_0_2_0) (headsOK_of_chunk census_0_2_1)) (headsOK_of_chunk census_0_2_2)) (headsOK_of_chunk census_0_2_3)

theorem census_0_3 : HeadsOK 0 3 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_0_3_0) (headsOK_of_chunk census_0_3_1)) (headsOK_of_chunk census_0_3_2)) (headsOK_of_chunk census_0_3_3)

theorem census_0_4 : HeadsOK 0 4 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_0_4_0) (headsOK_of_chunk census_0_4_1)) (headsOK_of_chunk census_0_4_2)) (headsOK_of_chunk census_0_4_3)

theorem census_0_5 : HeadsOK 0 5 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_0_5_0) (headsOK_of_chunk census_0_5_1)) (headsOK_of_chunk census_0_5_2)) (headsOK_of_chunk census_0_5_3)

theorem census_0_6 : HeadsOK 0 6 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_0_6_0) (headsOK_of_chunk census_0_6_1)) (headsOK_of_chunk census_0_6_2)) (headsOK_of_chunk census_0_6_3)

theorem census_1_0 : HeadsOK 1 0 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_1_0_0) (headsOK_of_chunk census_1_0_1)) (headsOK_of_chunk census_1_0_2)) (headsOK_of_chunk census_1_0_3)

theorem census_1_1 : HeadsOK 1 1 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_1_1_0) (headsOK_of_chunk census_1_1_1)) (headsOK_of_chunk census_1_1_2)) (headsOK_of_chunk census_1_1_3)

theorem census_1_2 : HeadsOK 1 2 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_1_2_0) (headsOK_of_chunk census_1_2_1)) (headsOK_of_chunk census_1_2_2)) (headsOK_of_chunk census_1_2_3)

theorem census_1_3 : HeadsOK 1 3 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_1_3_0) (headsOK_of_chunk census_1_3_1)) (headsOK_of_chunk census_1_3_2)) (headsOK_of_chunk census_1_3_3)

theorem census_1_4 : HeadsOK 1 4 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_1_4_0) (headsOK_of_chunk census_1_4_1)) (headsOK_of_chunk census_1_4_2)) (headsOK_of_chunk census_1_4_3)

theorem census_1_5 : HeadsOK 1 5 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_1_5_0) (headsOK_of_chunk census_1_5_1)) (headsOK_of_chunk census_1_5_2)) (headsOK_of_chunk census_1_5_3)

theorem census_1_6 : HeadsOK 1 6 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_1_6_0) (headsOK_of_chunk census_1_6_1)) (headsOK_of_chunk census_1_6_2)) (headsOK_of_chunk census_1_6_3)

theorem census_2_0 : HeadsOK 2 0 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_2_0_0) (headsOK_of_chunk census_2_0_1)) (headsOK_of_chunk census_2_0_2)) (headsOK_of_chunk census_2_0_3)

theorem census_2_1 : HeadsOK 2 1 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_2_1_0) (headsOK_of_chunk census_2_1_1)) (headsOK_of_chunk census_2_1_2)) (headsOK_of_chunk census_2_1_3)

theorem census_2_2 : HeadsOK 2 2 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_2_2_0) (headsOK_of_chunk census_2_2_1)) (headsOK_of_chunk census_2_2_2)) (headsOK_of_chunk census_2_2_3)

theorem census_2_3 : HeadsOK 2 3 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_2_3_0) (headsOK_of_chunk census_2_3_1)) (headsOK_of_chunk census_2_3_2)) (headsOK_of_chunk census_2_3_3)

theorem census_2_4 : HeadsOK 2 4 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_2_4_0) (headsOK_of_chunk census_2_4_1)) (headsOK_of_chunk census_2_4_2)) (headsOK_of_chunk census_2_4_3)

theorem census_2_5 : HeadsOK 2 5 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_2_5_0) (headsOK_of_chunk census_2_5_1)) (headsOK_of_chunk census_2_5_2)) (headsOK_of_chunk census_2_5_3)

theorem census_2_6 : HeadsOK 2 6 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_2_6_0) (headsOK_of_chunk census_2_6_1)) (headsOK_of_chunk census_2_6_2)) (headsOK_of_chunk census_2_6_3)

theorem census_3_0 : HeadsOK 3 0 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_3_0_0) (headsOK_of_chunk census_3_0_1)) (headsOK_of_chunk census_3_0_2)) (headsOK_of_chunk census_3_0_3)

theorem census_3_1 : HeadsOK 3 1 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_3_1_0) (headsOK_of_chunk census_3_1_1)) (headsOK_of_chunk census_3_1_2)) (headsOK_of_chunk census_3_1_3)

theorem census_3_2 : HeadsOK 3 2 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_3_2_0) (headsOK_of_chunk census_3_2_1)) (headsOK_of_chunk census_3_2_2)) (headsOK_of_chunk census_3_2_3)

theorem census_3_3 : HeadsOK 3 3 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_3_3_0) (headsOK_of_chunk census_3_3_1)) (headsOK_of_chunk census_3_3_2)) (headsOK_of_chunk census_3_3_3)

theorem census_3_4 : HeadsOK 3 4 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_3_4_0) (headsOK_of_chunk census_3_4_1)) (headsOK_of_chunk census_3_4_2)) (headsOK_of_chunk census_3_4_3)

theorem census_3_5 : HeadsOK 3 5 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_3_5_0) (headsOK_of_chunk census_3_5_1)) (headsOK_of_chunk census_3_5_2)) (headsOK_of_chunk census_3_5_3)

theorem census_3_6 : HeadsOK 3 6 61 80 0 (2 ^ 12) :=
  headsOK_append (headsOK_append (headsOK_append (headsOK_of_chunk census_3_6_0) (headsOK_of_chunk census_3_6_1)) (headsOK_of_chunk census_3_6_2)) (headsOK_of_chunk census_3_6_3)

/-- **The census**: every head of 12 cells at each of the 28 alignments passes the checker with the bound 61
and 80 rounds. -/
theorem census (a o : Nat) (ha : a < 4) (ho : o < 7) : HeadsOK a o 61 80 0 (2 ^ 12) :=
  match a, o, ha, ho with
  | 0, 0, _, _ => census_0_0
  | 0, 1, _, _ => census_0_1
  | 0, 2, _, _ => census_0_2
  | 0, 3, _, _ => census_0_3
  | 0, 4, _, _ => census_0_4
  | 0, 5, _, _ => census_0_5
  | 0, 6, _, _ => census_0_6
  | 1, 0, _, _ => census_1_0
  | 1, 1, _, _ => census_1_1
  | 1, 2, _, _ => census_1_2
  | 1, 3, _, _ => census_1_3
  | 1, 4, _, _ => census_1_4
  | 1, 5, _, _ => census_1_5
  | 1, 6, _, _ => census_1_6
  | 2, 0, _, _ => census_2_0
  | 2, 1, _, _ => census_2_1
  | 2, 2, _, _ => census_2_2
  | 2, 3, _, _ => census_2_3
  | 2, 4, _, _ => census_2_4
  | 2, 5, _, _ => census_2_5
  | 2, 6, _, _ => census_2_6
  | 3, 0, _, _ => census_3_0
  | 3, 1, _, _ => census_3_1
  | 3, 2, _, _ => census_3_2
  | 3, 3, _, _ => census_3_3
  | 3, 4, _, _ => census_3_4
  | 3, 5, _, _ => census_3_5
  | 3, 6, _, _ => census_3_6
  | a + 4, _, ha, _ => absurd ha (by omega)
  | _, o + 7, _, ho => absurd ho (by omega)


/-! ### Every head of up to 12 cells on the ether settles -/

/-- **The defect of every head of up to 12 cells on the ether stays below cell 61.** If the cells of `u` from
`p ≤ 12` on are the ether at the alignment `(a, o)`, then at every step `t` the cells from 61 on are the ether at phase
`a + t`. -/
theorem ether_tail_clear (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 12)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) :
    ∀ t j, 61 ≤ j → heldOrbit u t j = eth (a + t) (j + o) := by
  have hu' : ∀ j, 12 ≤ j → u j = eth (a % 4) (j + o % 7) := fun j hj => by
    rw [hu j (by omega)]; exact eth_congr (by omega) (by omega)
  have hc := clear_of_census (by decide) (by decide) (census (a % 4) (o % 7) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide))) hu'
  intro t j hj
  rw [heldOrbit_eq_defect u (a % 4) (o % 7) t j, hc t j hj, Bool.false_xor]
  exact eth_congr (by omega) (by omega)

/-- **Every head of up to 12 cells on the ether has an eventually periodic orbit.** -/
theorem ether_tail_eventually_periodic (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 12)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) :
    ∃ T P, 0 < P ∧ ∀ t, T ≤ t → heldOrbit u (t + P) = heldOrbit u t := by
  refine eventually_periodic_of_clear (a := a) (o := o) (L := 61) fun t j hj => ?_
  unfold defect
  rw [ether_tail_clear u a o p hp hu t j hj]
  cases eth (a + t) (j + o) <;> rfl

/-- **Conjecture (R) for the ether tails of up to 12 cells**: every 2-adic integer whose bits from `p ≤ 12` on are the
ether at one of its alignments, in `InK` or not, has an eventually periodic itinerary. -/
theorem ether_tail_itinerary (u : Nat → Bool) (a o p : Nat) (hp : p ≤ 12)
    (hu : ∀ j, p ≤ j → u j = eth a (j + o)) :
    ∃ pre n, 0 < n ∧ ∀ s, pre ≤ s → itinerary u (s + n) = itinerary u s := by
  obtain ⟨T, P, hP, h⟩ := ether_tail_eventually_periodic u a o p hp hu
  exact itinerary_of_eventually_periodic hP h

end Rule30Open
