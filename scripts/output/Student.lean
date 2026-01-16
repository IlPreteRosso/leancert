/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors (auto-generated)
-/
import LeanCert.ML.Transformer
import LeanCert.ML.LayerNormAffine

set_option linter.unnecessarySeqFocus false

/-!
# Transformer Encoder: student

Student transformer

## Architecture

- **Layers**: 1
- **Model Dimension**: 8
- **FFN Hidden Dimension**: 16

## Affine Arithmetic

LayerNorm uses affine arithmetic for tight bounds by tracking
correlations between variables. This avoids the "dependency problem"
where standard interval arithmetic loses correlation information.
-/

namespace DistillationTest.Student

open LeanCert.Core
open LeanCert.ML
open LeanCert.ML.Transformer
open IntervalVector

/-! ## Layer 1 -/

/-- Pre-FFN LayerNorm -/
def studentBlock1LN1Gamma : List ℚ := [((5475 : ℚ) / 5581), ((7167 : ℚ) / 7244), ((2116 : ℚ) / 2111), ((6881 : ℚ) / 7010), ((6342 : ℚ) / 6319), ((6064 : ℚ) / 6451), ((6181 : ℚ) / 6015), ((9887 : ℚ) / 9587)]
def studentBlock1LN1Beta : List ℚ := [((31 : ℚ) / 9968), (((-172) : ℚ) / 9623), ((295 : ℚ) / 8191), ((33 : ℚ) / 5675), (((-156) : ℚ) / 4393), (((-49) : ℚ) / 1020), ((227 : ℚ) / 5122), (((-58) : ℚ) / 1851)]
def studentBlock1LN1Epsilon : ℚ := ((1 : ℚ) / 100000)
def studentBlock1LN1 : LayerNormParams where
  gamma := studentBlock1LN1Gamma
  beta := studentBlock1LN1Beta
  epsilon := studentBlock1LN1Epsilon
  epsilon_pos := by simp only [studentBlock1LN1Epsilon]; norm_num

/-- Feed-Forward Network -/
def studentBlock1FFNLinear1Weights : List (List ℚ) := [
  [(((-1477) : ℚ) / 8201), (((-485) : ℚ) / 2162), (((-160) : ℚ) / 1749), ((1143 : ℚ) / 5447), ((2481 : ℚ) / 8207), (((-1840) : ℚ) / 9727), ((2228 : ℚ) / 6473), (((-119) : ℚ) / 8784)],
  [(((-520) : ℚ) / 2637), (((-715) : ℚ) / 9539), ((269 : ℚ) / 1363), ((1714 : ℚ) / 6815), ((2706 : ℚ) / 8347), (((-583) : ℚ) / 7393), (((-2657) : ℚ) / 8706), (((-854) : ℚ) / 9287)],
  [((161 : ℚ) / 6500), ((626 : ℚ) / 4899), ((1359 : ℚ) / 3587), (((-266) : ℚ) / 9927), (((-1019) : ℚ) / 2202), (((-1438) : ℚ) / 8443), ((1767 : ℚ) / 7678), ((396 : ℚ) / 2707)],
  [(((-343) : ℚ) / 7617), ((29 : ℚ) / 995), (((-1083) : ℚ) / 9691), (((-699) : ℚ) / 8591), (((-1321) : ℚ) / 5592), (((-1019) : ℚ) / 9409), ((2426 : ℚ) / 9441), (((-769) : ℚ) / 4361)],
  [((29 : ℚ) / 5049), (((-671) : ℚ) / 3112), (((-1581) : ℚ) / 5078), ((1443 : ℚ) / 3970), (((-137) : ℚ) / 6203), (((-1320) : ℚ) / 9991), ((2372 : ℚ) / 8495), (((-117) : ℚ) / 8656)],
  [((96 : ℚ) / 4865), ((19 : ℚ) / 598), (((-2612) : ℚ) / 9381), ((886 : ℚ) / 2969), ((1567 : ℚ) / 4624), (((-987) : ℚ) / 8405), ((22 : ℚ) / 1643), ((483 : ℚ) / 6248)],
  [(((-190) : ℚ) / 563), ((2133 : ℚ) / 9409), ((122 : ℚ) / 1859), ((1814 : ℚ) / 8513), ((1 : ℚ) / 456), (((-739) : ℚ) / 7331), ((2119 : ℚ) / 8558), ((1565 : ℚ) / 7664)],
  [((13 : ℚ) / 8427), (((-86) : ℚ) / 3931), (((-613) : ℚ) / 8734), ((284 : ℚ) / 5289), ((233 : ℚ) / 8802), ((3335 : ℚ) / 8141), ((135 : ℚ) / 7001), (((-1009) : ℚ) / 2180)],
  [(((-753) : ℚ) / 2393), (((-2281) : ℚ) / 7031), ((1379 : ℚ) / 6764), (((-1599) : ℚ) / 5698), ((396 : ℚ) / 4049), (((-1239) : ℚ) / 7624), (((-1997) : ℚ) / 9653), (((-2737) : ℚ) / 7782)],
  [(((-1505) : ℚ) / 8583), ((1495 : ℚ) / 6763), (((-623) : ℚ) / 8791), ((1754 : ℚ) / 8149), (((-2909) : ℚ) / 8623), ((1625 : ℚ) / 7758), (((-1077) : ℚ) / 6836), (((-908) : ℚ) / 8747)],
  [((217 : ℚ) / 1978), ((101 : ℚ) / 380), (((-2008) : ℚ) / 7621), (((-3221) : ℚ) / 9493), ((4312 : ℚ) / 9245), ((2191 : ℚ) / 9236), (((-1513) : ℚ) / 6389), (((-1903) : ℚ) / 9522)],
  [(((-657) : ℚ) / 8146), (((-2237) : ℚ) / 9763), ((1046 : ℚ) / 7007), (((-1768) : ℚ) / 9965), (((-496) : ℚ) / 1691), ((5 : ℚ) / 8107), ((858 : ℚ) / 8863), ((1042 : ℚ) / 8369)],
  [(((-663) : ℚ) / 5266), ((2208 : ℚ) / 7565), (((-33) : ℚ) / 3989), (((-1474) : ℚ) / 4453), (((-67) : ℚ) / 3281), (((-2287) : ℚ) / 7901), ((800 : ℚ) / 6657), ((355 : ℚ) / 2009)],
  [((2187 : ℚ) / 8578), ((857 : ℚ) / 7442), ((2977 : ℚ) / 9916), (((-234) : ℚ) / 5959), (((-74) : ℚ) / 9633), ((213 : ℚ) / 8866), ((3311 : ℚ) / 9355), (((-1140) : ℚ) / 4091)],
  [((1849 : ℚ) / 8773), ((2089 : ℚ) / 8926), ((777 : ℚ) / 6539), ((1895 : ℚ) / 9426), ((133 : ℚ) / 1658), (((-996) : ℚ) / 8003), (((-2104) : ℚ) / 9609), (((-845) : ℚ) / 6746)],
  [((1041 : ℚ) / 5216), (((-521) : ℚ) / 9406), ((1419 : ℚ) / 9016), ((227 : ℚ) / 607), ((1904 : ℚ) / 6775), (((-209) : ℚ) / 9092), ((806 : ℚ) / 2393), (((-207) : ℚ) / 1498)]
]
def studentBlock1FFNLinear1Bias : List ℚ := [(((-2365) : ℚ) / 9668), (((-75) : ℚ) / 9872), ((271 : ℚ) / 6471), ((2369 : ℚ) / 9677), (((-1813) : ℚ) / 8019), ((240 : ℚ) / 4027), ((1762 : ℚ) / 5905), (((-1257) : ℚ) / 6424), (((-378) : ℚ) / 2507), ((2925 : ℚ) / 8402), (((-221) : ℚ) / 4032), ((23 : ℚ) / 3425), (((-1597) : ℚ) / 7513), ((423 : ℚ) / 9139), (((-1111) : ℚ) / 5904), (((-459) : ℚ) / 6010)]
def studentBlock1FFNLinear1 : Layer where
  weights := studentBlock1FFNLinear1Weights
  bias := studentBlock1FFNLinear1Bias

def studentBlock1FFNLinear2Weights : List (List ℚ) := [
  [(((-295) : ℚ) / 9932), (((-231) : ℚ) / 9826), (((-1867) : ℚ) / 9727), ((522 : ℚ) / 8807), ((3 : ℚ) / 14), (((-91) : ℚ) / 1436), ((4 : ℚ) / 1985), (((-1859) : ℚ) / 9440), (((-8) : ℚ) / 785), ((38 : ℚ) / 191), (((-213) : ℚ) / 7309), ((411 : ℚ) / 5093), (((-1347) : ℚ) / 8219), (((-238) : ℚ) / 2923), (((-274) : ℚ) / 3121), (((-339) : ℚ) / 6581)],
  [(((-167) : ℚ) / 9676), (((-246) : ℚ) / 5593), ((37 : ℚ) / 2245), ((5 : ℚ) / 9469), (((-1195) : ℚ) / 5216), ((1245 : ℚ) / 9832), (((-687) : ℚ) / 6131), ((199 : ℚ) / 8681), ((83 : ℚ) / 8164), (((-1228) : ℚ) / 7933), ((324 : ℚ) / 6901), (((-2040) : ℚ) / 8327), (((-5) : ℚ) / 4502), ((343 : ℚ) / 7675), ((307 : ℚ) / 1816), (((-1219) : ℚ) / 9158)],
  [(((-582) : ℚ) / 2489), (((-2208) : ℚ) / 9859), (((-903) : ℚ) / 7388), ((58 : ℚ) / 401), ((70 : ℚ) / 9329), (((-243) : ℚ) / 8707), (((-49) : ℚ) / 8441), (((-138) : ℚ) / 1405), ((179 : ℚ) / 2579), ((57 : ℚ) / 3316), ((226 : ℚ) / 1807), (((-1645) : ℚ) / 9971), (((-1089) : ℚ) / 5477), (((-1937) : ℚ) / 9626), ((25 : ℚ) / 4818), ((101 : ℚ) / 9935)],
  [((339 : ℚ) / 8423), ((209 : ℚ) / 6965), ((1019 : ℚ) / 4088), ((419 : ℚ) / 1792), ((1901 : ℚ) / 8614), (((-906) : ℚ) / 5069), ((220 : ℚ) / 9443), ((173 : ℚ) / 7711), ((695 : ℚ) / 4223), ((569 : ℚ) / 2768), (((-202) : ℚ) / 1273), ((69 : ℚ) / 1532), (((-677) : ℚ) / 5651), (((-207) : ℚ) / 4792), (((-1193) : ℚ) / 7033), (((-21) : ℚ) / 9292)],
  [(((-236) : ℚ) / 3427), (((-682) : ℚ) / 9091), ((1135 : ℚ) / 9068), ((661 : ℚ) / 5219), (((-1762) : ℚ) / 8373), ((256 : ℚ) / 5701), (((-1711) : ℚ) / 9774), ((2399 : ℚ) / 8783), (((-1645) : ℚ) / 8599), ((37 : ℚ) / 2993), (((-2034) : ℚ) / 8083), ((578 : ℚ) / 6577), ((2218 : ℚ) / 8937), ((1791 : ℚ) / 9544), (((-99) : ℚ) / 2803), (((-1141) : ℚ) / 7111)],
  [(((-343) : ℚ) / 3124), (((-1109) : ℚ) / 7882), (((-979) : ℚ) / 4955), (((-383) : ℚ) / 7657), (((-480) : ℚ) / 7541), ((333 : ℚ) / 8906), (((-783) : ℚ) / 5932), (((-1367) : ℚ) / 6167), (((-1706) : ℚ) / 7785), ((1924 : ℚ) / 8823), (((-717) : ℚ) / 4462), ((1328 : ℚ) / 9691), ((641 : ℚ) / 3026), ((1448 : ℚ) / 8889), ((276 : ℚ) / 6263), (((-1889) : ℚ) / 7928)],
  [(((-51) : ℚ) / 4813), ((180 : ℚ) / 1747), (((-1651) : ℚ) / 8882), ((13 : ℚ) / 9069), (((-998) : ℚ) / 9993), (((-1007) : ℚ) / 6740), ((1136 : ℚ) / 9459), ((578 : ℚ) / 3821), ((1564 : ℚ) / 7547), (((-189) : ℚ) / 965), ((1715 : ℚ) / 9046), (((-511) : ℚ) / 9964), ((137 : ℚ) / 5779), ((246 : ℚ) / 6641), ((1036 : ℚ) / 9859), ((323 : ℚ) / 6808)],
  [(((-267) : ℚ) / 6364), ((803 : ℚ) / 8336), (((-992) : ℚ) / 8279), ((266 : ℚ) / 3281), (((-952) : ℚ) / 3777), ((181 : ℚ) / 5548), (((-423) : ℚ) / 5473), ((2115 : ℚ) / 9941), ((339 : ℚ) / 4729), ((1077 : ℚ) / 6932), (((-249) : ℚ) / 5495), ((917 : ℚ) / 9985), ((1403 : ℚ) / 5849), (((-1576) : ℚ) / 4913), ((771 : ℚ) / 8384), (((-1342) : ℚ) / 7353)]
]
def studentBlock1FFNLinear2Bias : List ℚ := [(((-484) : ℚ) / 7273), ((767 : ℚ) / 5738), ((454 : ℚ) / 3307), ((1127 : ℚ) / 8748), ((649 : ℚ) / 2935), ((1117 : ℚ) / 5451), (((-1001) : ℚ) / 9497), (((-2254) : ℚ) / 8971)]
def studentBlock1FFNLinear2 : Layer where
  weights := studentBlock1FFNLinear2Weights
  bias := studentBlock1FFNLinear2Bias

/-- FFN Block: 8 → 16 → 8 -/
def studentBlock1FFN : FFNBlock where
  linear1 := studentBlock1FFNLinear1
  linear2 := studentBlock1FFNLinear2
  dims_match := by simp [studentBlock1FFNLinear1, studentBlock1FFNLinear2, studentBlock1FFNLinear1Weights, studentBlock1FFNLinear2Weights, Layer.inputDim, Layer.outputDim, studentBlock1FFNLinear1Bias]

/-- Post-FFN LayerNorm -/
def studentBlock1LN2Gamma : List ℚ := [((7123 : ℚ) / 6972), ((10071 : ℚ) / 9400), ((8129 : ℚ) / 8332), ((7713 : ℚ) / 7634), ((6607 : ℚ) / 6704), ((2629 : ℚ) / 2471), ((9697 : ℚ) / 9792), ((3082 : ℚ) / 3157)]
def studentBlock1LN2Beta : List ℚ := [((49 : ℚ) / 1691), (((-311) : ℚ) / 9629), (((-245) : ℚ) / 8612), ((274 : ℚ) / 9079), ((229 : ℚ) / 8510), ((249 : ℚ) / 7858), ((3 : ℚ) / 104), ((215 : ℚ) / 8849)]
def studentBlock1LN2Epsilon : ℚ := ((1 : ℚ) / 100000)
def studentBlock1LN2 : LayerNormParams where
  gamma := studentBlock1LN2Gamma
  beta := studentBlock1LN2Beta
  epsilon := studentBlock1LN2Epsilon
  epsilon_pos := by simp only [studentBlock1LN2Epsilon]; norm_num

/-- Transformer Block: dim=8, hidden=16 -/
def studentBlock1 : TransformerBlock where
  ln1 := studentBlock1LN1
  ffn := studentBlock1FFN
  ln2 := studentBlock1LN2

/-- All transformer blocks -/
def studentBlocks : List TransformerBlock := [studentBlock1]

/-! ## Input Domain and Verification -/

def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := -53) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec

/-- Input domain -/
def studentInput : IntervalVector := [mkInterval (-1) 1, mkInterval (-1) 1, mkInterval (-1) 1, mkInterval (-1) 1, mkInterval (-1) 1, mkInterval (-1) 1, mkInterval (-1) 1, mkInterval (-1) 1]

/-- Forward pass with affine arithmetic for tight LayerNorm bounds -/
def studentForward (x : IntervalVector) (prec : Int := -53) : IntervalVector :=
  studentBlocks.foldl (fun acc blk => blk.forwardIntervalTight acc prec) x

/-- Computed output bounds -/
def studentOutputBounds : IntervalVector := studentForward studentInput (-53)

#eval studentOutputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))

end DistillationTest.Student