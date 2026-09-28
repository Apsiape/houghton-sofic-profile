import FreeReduction
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WordCertificate
-- Generated from SHA-256 f63563a1f8e1f8cde46620ccefd1085840c35198b10e6f4bc568f39354693149
def word (s : String) : Word := s.toList.map fun c =>
  match c with
  | 'a' => .a | 'A' => .A | 'b' => .b | 'B' => .B | 'x' => .x | _ => .X
-- r6
def cells_0 : List Cell := [
  ⟨word "AAxa", 3, false⟩,
  ⟨word "AAxaxA", 3, false⟩,
  ⟨word "AAxaxAxbXaBX", 3, true⟩,
  ⟨word "AAxaxAxbXBX", 3, true⟩,
  ⟨word "AAxaxAxaXA", 4, false⟩,
  ⟨word "AAxaxAxa", 0, true⟩,
  ⟨word "AAxaxAxaxA", 0, true⟩,
  ⟨word "AAxaxAxaxAxa", 0, true⟩,
  ⟨word "AA", 1, false⟩]
def target_0 : Word := word "AAxaabAAXaaB"
theorem area_count_0 : cells_0.length = 9 := by decide
theorem step_0_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_0_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxaxAxaxa") = M.one :=
  checked_step M h ⟨word "AA", 1, false⟩ (word "") (word "AAxaxAxaxAxaxa")
    (by decide) (step_0_0 M h)
theorem step_0_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxaxAxaXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxaxAxa", 0, true⟩ (word "AAxaxAxaxAxaxa") (word "AAxaxAxaxAxaXa")
    (by decide) (step_0_1 M h)
theorem step_0_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxaxAXaXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxaxA", 0, true⟩ (word "AAxaxAxaxAxaXa") (word "AAxaxAxaxAXaXa")
    (by decide) (step_0_2 M h)
theorem step_0_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxaXAXaXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxa", 0, true⟩ (word "AAxaxAxaxAXaXa") (word "AAxaxAxaXAXaXa")
    (by decide) (step_0_3 M h)
theorem step_0_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxbXBXaXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxaXA", 4, false⟩ (word "AAxaxAxaXAXaXa") (word "AAxaxAxbXBXaXa")
    (by decide) (step_0_4 M h)
theorem step_0_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxbXaBXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxbXBX", 3, true⟩ (word "AAxaxAxbXBXaXa") (word "AAxaxAxbXaBXa")
    (by decide) (step_0_5 M h)
theorem step_0_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxbXaaB") = M.one :=
  checked_step M h ⟨word "AAxaxAxbXaBX", 3, true⟩ (word "AAxaxAxbXaBXa") (word "AAxaxAxbXaaB")
    (by decide) (step_0_6 M h)
theorem step_0_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxbAXaaB") = M.one :=
  checked_step M h ⟨word "AAxaxA", 3, false⟩ (word "AAxaxAxbXaaB") (word "AAxaxbAXaaB")
    (by decide) (step_0_7 M h)
theorem step_0_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaabAAXaaB") = M.one :=
  checked_step M h ⟨word "AAxa", 3, false⟩ (word "AAxaxbAXaaB") (word "AAxaabAAXaaB")
    (by decide) (step_0_8 M h)
theorem semantic_0 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_0 = M.one := by
  have endcheck : reduce target_0 = reduce (word "AAxaabAAXaaB") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_0_9 M h)
#check semantic_0
-- D1
def cells_1 : List Cell := [
  ⟨word "a", 3, false⟩,
  ⟨word "axb", 3, false⟩,
  ⟨word "axbxBA", 3, false⟩,
  ⟨word "axbxBAxb", 3, false⟩,
  ⟨word "axbxBAx", 4, true⟩,
  ⟨word "ax", 4, true⟩,
  ⟨word "axA", 2, true⟩,
  ⟨word "axAxaaxA", 0, false⟩,
  ⟨word "axAxaaxAX", 3, false⟩,
  ⟨word "axAxaaxAb", 3, false⟩,
  ⟨word "axAxaaxAbxBA", 3, false⟩,
  ⟨word "axAxaaxAbxBAxb", 3, false⟩,
  ⟨word "axAxaaxAbxBAx", 4, true⟩,
  ⟨word "axAxaaxA", 4, true⟩,
  ⟨word "axAxaaxAA", 2, true⟩,
  ⟨word "axAxaaxAAxaaxA", 0, false⟩,
  ⟨word "axAx", 2, true⟩,
  ⟨word "axA", 0, false⟩,
  ⟨word "axa", 0, false⟩]
def target_1 : Word := word "aabbAABBaabbAABB"
theorem area_count_1 : cells_1.length = 19 := by decide
theorem step_1_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_1_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxxAXA") = M.one :=
  checked_step M h ⟨word "axa", 0, false⟩ (word "") (word "axaxxAXA")
    (by decide) (step_1_0 M h)
theorem step_1_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxxaaxxAXA") = M.one :=
  checked_step M h ⟨word "axA", 0, false⟩ (word "axaxxAXA") (word "axAxxaaxxAXA")
    (by decide) (step_1_1 M h)
theorem step_1_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAAxaaxAXA") = M.one :=
  checked_step M h ⟨word "axAx", 2, true⟩ (word "axAxxaaxxAXA") (word "axAxaaxAAxaaxAXA")
    (by decide) (step_1_2 M h)
theorem step_1_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAAxaaxAxA") = M.one :=
  checked_step M h ⟨word "axAxaaxAAxaaxA", 0, false⟩ (word "axAxaaxAAxaaxAXA") (word "axAxaaxAAxaaxAxA")
    (by decide) (step_1_3 M h)
theorem step_1_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxxAAxaxA") = M.one :=
  checked_step M h ⟨word "axAxaaxAA", 2, true⟩ (word "axAxaaxAAxaaxAxA") (word "axAxaaxxAAxaxA")
    (by decide) (step_1_4 M h)
theorem step_1_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAbxBAxaxA") = M.one :=
  checked_step M h ⟨word "axAxaaxA", 4, true⟩ (word "axAxaaxxAAxaxA") (word "axAxaaxAbxBAxaxA")
    (by decide) (step_1_5 M h)
theorem step_1_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAbxBAxbxB") = M.one :=
  checked_step M h ⟨word "axAxaaxAbxBAx", 4, true⟩ (word "axAxaaxAbxBAxaxA") (word "axAxaaxAbxBAxbxB")
    (by decide) (step_1_6 M h)
theorem step_1_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAbxBAxbabABB") = M.one :=
  checked_step M h ⟨word "axAxaaxAbxBAxb", 3, false⟩ (word "axAxaaxAbxBAxbxB") (word "axAxaaxAbxBAxbabABB")
    (by decide) (step_1_7 M h)
theorem step_1_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAbxbABB") = M.one :=
  checked_step M h ⟨word "axAxaaxAbxBA", 3, false⟩ (word "axAxaaxAbxBAxbabABB") (word "axAxaaxAbxbABB")
    (by decide) (step_1_8 M h)
theorem step_1_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAbabAABB") = M.one :=
  checked_step M h ⟨word "axAxaaxAb", 3, false⟩ (word "axAxaaxAbxbABB") (word "axAxaaxAbabAABB")
    (by decide) (step_1_9 M h)
theorem step_1_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAXabbAABB") = M.one :=
  checked_step M h ⟨word "axAxaaxAX", 3, false⟩ (word "axAxaaxAbabAABB") (word "axAxaaxAXabbAABB")
    (by decide) (step_1_10 M h)
theorem step_1_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaaxAxabbAABB") = M.one :=
  checked_step M h ⟨word "axAxaaxA", 0, false⟩ (word "axAxaaxAXabbAABB") (word "axAxaaxAxabbAABB")
    (by decide) (step_1_11 M h)
theorem step_1_13 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaxabbAABB") = M.one :=
  checked_step M h ⟨word "axA", 2, true⟩ (word "axAxaaxAxabbAABB") (word "axaxAAxaxabbAABB")
    (by decide) (step_1_12 M h)
theorem step_1_14 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBAxaxabbAABB") = M.one :=
  checked_step M h ⟨word "ax", 4, true⟩ (word "axaxAAxaxabbAABB") (word "axbxBAxaxabbAABB")
    (by decide) (step_1_13 M h)
theorem step_1_15 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBAxbxBaabbAABB") = M.one :=
  checked_step M h ⟨word "axbxBAx", 4, true⟩ (word "axbxBAxaxabbAABB") (word "axbxBAxbxBaabbAABB")
    (by decide) (step_1_14 M h)
theorem step_1_16 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBAxbabABBaabbAABB") = M.one :=
  checked_step M h ⟨word "axbxBAxb", 3, false⟩ (word "axbxBAxbxBaabbAABB") (word "axbxBAxbabABBaabbAABB")
    (by decide) (step_1_15 M h)
theorem step_1_17 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxbABBaabbAABB") = M.one :=
  checked_step M h ⟨word "axbxBA", 3, false⟩ (word "axbxBAxbabABBaabbAABB") (word "axbxbABBaabbAABB")
    (by decide) (step_1_16 M h)
theorem step_1_18 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbabAABBaabbAABB") = M.one :=
  checked_step M h ⟨word "axb", 3, false⟩ (word "axbxbABBaabbAABB") (word "axbabAABBaabbAABB")
    (by decide) (step_1_17 M h)
theorem step_1_19 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabbAABBaabbAABB") = M.one :=
  checked_step M h ⟨word "a", 3, false⟩ (word "axbabAABBaabbAABB") (word "aabbAABBaabbAABB")
    (by decide) (step_1_18 M h)
theorem semantic_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_1 = M.one := by
  have endcheck : reduce target_1 = reduce (word "aabbAABBaabbAABB") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_1_19 M h)
#check semantic_1
-- D4
def cells_2 : List Cell := [
]
def target_2 : Word := word "aabbAABBbbaaBBAA"
theorem area_count_2 : cells_2.length = 0 := by decide
theorem step_2_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem semantic_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_2 = M.one := by
  have endcheck : reduce target_2 = reduce (word "") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_2_0 M h)
#check semantic_2
-- dt
def cells_3 : List Cell := [
  ⟨word "BaBA", 3, false⟩]
def target_3 : Word := word "BBaaAAXaaAbAb"
theorem area_count_3 : cells_3.length = 1 := by decide
theorem step_3_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_3_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BBXabAb") = M.one :=
  checked_step M h ⟨word "BaBA", 3, false⟩ (word "") (word "BBXabAb")
    (by decide) (step_3_0 M h)
theorem semantic_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_3 = M.one := by
  have endcheck : reduce target_3 = reduce (word "BBXabAb") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_3_1 M h)
#check semantic_3
-- ot
def cells_4 : List Cell := [
  ⟨word "BBaBA", 3, false⟩,
  ⟨word "BaBA", 3, false⟩,
  ⟨word "BaBAxaaBA", 3, false⟩,
  ⟨word "BaBAxaaBAxabAAxaaBA", 3, false⟩,
  ⟨word "BaBAxaaBAxabAAxaaBAxA", 3, false⟩,
  ⟨word "BaBAxaaBAxabAAxaaBAxAxbXaBX", 3, true⟩,
  ⟨word "BaBAxaaBAxabAAxaaBAxAxbXBX", 3, true⟩,
  ⟨word "BaBAxaaBAxabAAxaaBAxAxaXA", 4, false⟩,
  ⟨word "BaBAxaaBAxabAAxaaBAxAxa", 0, true⟩,
  ⟨word "BaBAxaaBAxabAAxaaBAxAxaxA", 0, true⟩,
  ⟨word "BaBAxaaBAxabAAxaaBAxAxaxAxa", 0, true⟩,
  ⟨word "BaBAxaaBAxabAAxaaBAAX", 1, false⟩]
def target_4 : Word := word "BBBaabAAXaaBaAAXaaAbAbBaAAXaaAbAb"
theorem area_count_4 : cells_4.length = 12 := by decide
theorem step_4_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_4_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxabAAxaaBAxAxaxAxaxAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBAAX", 1, false⟩ (word "") (word "BaBAxaaBAxabAAxaaBAxAxaxAxaxAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_0 M h)
theorem step_4_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxabAAxaaBAxAxaxAxaXAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBAxAxaxAxa", 0, true⟩ (word "BaBAxaaBAxabAAxaaBAxAxaxAxaxAxaabAAXaaBAXabAAXabAb") (word "BaBAxaaBAxabAAxaaBAxAxaxAxaXAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_1 M h)
theorem step_4_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxabAAxaaBAxAxaxAXaXAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBAxAxaxA", 0, true⟩ (word "BaBAxaaBAxabAAxaaBAxAxaxAxaXAxaabAAXaaBAXabAAXabAb") (word "BaBAxaaBAxabAAxaaBAxAxaxAXaXAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_2 M h)
theorem step_4_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxabAAxaaBAxAxaXAXaXAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBAxAxa", 0, true⟩ (word "BaBAxaaBAxabAAxaaBAxAxaxAXaXAxaabAAXaaBAXabAAXabAb") (word "BaBAxaaBAxabAAxaaBAxAxaXAXaXAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_3 M h)
theorem step_4_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxabAAxaaBAxAxbXBXaXAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBAxAxaXA", 4, false⟩ (word "BaBAxaaBAxabAAxaaBAxAxaXAXaXAxaabAAXaaBAXabAAXabAb") (word "BaBAxaaBAxabAAxaaBAxAxbXBXaXAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_4 M h)
theorem step_4_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxabAAxaaBAxAxbXaBXAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBAxAxbXBX", 3, true⟩ (word "BaBAxaaBAxabAAxaaBAxAxbXBXaXAxaabAAXaaBAXabAAXabAb") (word "BaBAxaaBAxabAAxaaBAxAxbXaBXAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_5 M h)
theorem step_4_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxabAAxaaBAxAxbXaaBAAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBAxAxbXaBX", 3, true⟩ (word "BaBAxaaBAxabAAxaaBAxAxbXaBXAxaabAAXaaBAXabAAXabAb") (word "BaBAxaaBAxabAAxaaBAxAxbXaaBAAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_6 M h)
theorem step_4_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxabAAxaaBAxbAXaaBAAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBAxA", 3, false⟩ (word "BaBAxaaBAxabAAxaaBAxAxbXaaBAAxaabAAXaaBAXabAAXabAb") (word "BaBAxaaBAxabAAxaaBAxbAXaaBAAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_7 M h)
theorem step_4_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaaBAxAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBAxabAAxaaBA", 3, false⟩ (word "BaBAxaaBAxabAAxaaBAxbAXaaBAAxaabAAXaaBAXabAAXabAb") (word "BaBAxaaBAxAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_8 M h)
theorem step_4_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BaBAxaBAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBAxaaBA", 3, false⟩ (word "BaBAxaaBAxAxaabAAXaaBAXabAAXabAb") (word "BaBAxaBAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_9 M h)
theorem step_4_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BBaBAxaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BaBA", 3, false⟩ (word "BaBAxaBAxaabAAXaaBAXabAAXabAb") (word "BBaBAxaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_10 M h)
theorem step_4_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BBBaabAAXaaBAXabAAXabAb") = M.one :=
  checked_step M h ⟨word "BBaBA", 3, false⟩ (word "BBaBAxaabAAXaaBAXabAAXabAb") (word "BBBaabAAXaaBAXabAAXabAb")
    (by decide) (step_4_11 M h)
theorem semantic_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_4 = M.one := by
  have endcheck : reduce target_4 = reduce (word "BBBaabAAXaaBAXabAAXabAb") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_4_12 M h)
#check semantic_4
-- F2
def cells_5 : List Cell := [
  ⟨word "", 2, false⟩]
def target_5 : Word := word "xaaxAAXaaXAA"
theorem area_count_5 : cells_5.length = 1 := by decide
theorem step_5_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_5_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaaxAAXaaXAA") = M.one :=
  checked_step M h ⟨word "", 2, false⟩ (word "") (word "xaaxAAXaaXAA")
    (by decide) (step_5_0 M h)
theorem semantic_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_5 = M.one := by
  have endcheck : reduce target_5 = reduce (word "xaaxAAXaaXAA") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_5_1 M h)
#check semantic_5
-- F3
def cells_6 : List Cell := [
  ⟨word "aa", 4, false⟩,
  ⟨word "aabxBAAxaaaXA", 4, true⟩,
  ⟨word "aabxBAAxa", 3, false⟩,
  ⟨word "aabxBAAxaxA", 3, false⟩,
  ⟨word "aabxBAAxaxAxbXaBX", 3, true⟩,
  ⟨word "aabxBAAxaxAxbXBX", 3, true⟩,
  ⟨word "aabxBAAxaxAxaXA", 4, false⟩,
  ⟨word "aabxBAAxaxAxa", 0, true⟩,
  ⟨word "aabxBAAxaxAxaxA", 0, true⟩,
  ⟨word "aabxBAAxaxAxaxAxa", 0, true⟩,
  ⟨word "aabxBAA", 1, false⟩,
  ⟨word "aabxAAxaaXAAX", 2, true⟩,
  ⟨word "", 1, true⟩,
  ⟨word "xaxAxaxAxa", 0, false⟩,
  ⟨word "xaxAxaxA", 0, false⟩,
  ⟨word "xaxAxa", 0, false⟩,
  ⟨word "xaxAxaXA", 4, true⟩,
  ⟨word "xaxAxbXBX", 3, false⟩,
  ⟨word "xaxAxbXaBX", 3, false⟩,
  ⟨word "xaxA", 3, true⟩,
  ⟨word "xa", 3, true⟩]
def target_6 : Word := word "aaaxAAAxaaaXAAAX"
theorem area_count_6 : cells_6.length = 21 := by decide
theorem step_6_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_6_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxbaBAAX") = M.one :=
  checked_step M h ⟨word "xa", 3, true⟩ (word "") (word "xaxbaBAAX")
    (by decide) (step_6_0 M h)
theorem step_6_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxbaaBAAX") = M.one :=
  checked_step M h ⟨word "xaxA", 3, true⟩ (word "xaxbaBAAX") (word "xaxAxbaaBAAX")
    (by decide) (step_6_1 M h)
theorem step_6_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxbXaBXabAAxaaBAAX") = M.one :=
  checked_step M h ⟨word "xaxAxbXaBX", 3, false⟩ (word "xaxAxbaaBAAX") (word "xaxAxbXaBXabAAxaaBAAX")
    (by decide) (step_6_2 M h)
theorem step_6_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxbXBXaXabAAxaaBAAX") = M.one :=
  checked_step M h ⟨word "xaxAxbXBX", 3, false⟩ (word "xaxAxbXaBXabAAxaaBAAX") (word "xaxAxbXBXaXabAAxaaBAAX")
    (by decide) (step_6_3 M h)
theorem step_6_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaXAXaXabAAxaaBAAX") = M.one :=
  checked_step M h ⟨word "xaxAxaXA", 4, true⟩ (word "xaxAxbXBXaXabAAxaaBAAX") (word "xaxAxaXAXaXabAAxaaBAAX")
    (by decide) (step_6_4 M h)
theorem step_6_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAXaXabAAxaaBAAX") = M.one :=
  checked_step M h ⟨word "xaxAxa", 0, false⟩ (word "xaxAxaXAXaXabAAxaaBAAX") (word "xaxAxaxAXaXabAAxaaBAAX")
    (by decide) (step_6_5 M h)
theorem step_6_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAxaXabAAxaaBAAX") = M.one :=
  checked_step M h ⟨word "xaxAxaxA", 0, false⟩ (word "xaxAxaxAXaXabAAxaaBAAX") (word "xaxAxaxAxaXabAAxaaBAAX")
    (by decide) (step_6_6 M h)
theorem step_6_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAxaxabAAxaaBAAX") = M.one :=
  checked_step M h ⟨word "xaxAxaxAxa", 0, false⟩ (word "xaxAxaxAxaXabAAxaaBAAX") (word "xaxAxaxAxaxabAAxaaBAAX")
    (by decide) (step_6_7 M h)
theorem step_6_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaBAAX") = M.one :=
  checked_step M h ⟨word "", 1, true⟩ (word "xaxAxaxAxaxabAAxaaBAAX") (word "aabAAxaaBAAX")
    (by decide) (step_6_8 M h)
theorem step_6_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxAAxaaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxAAxaaXAAX", 2, true⟩ (word "aabAAxaaBAAX") (word "aabxAAxaaXBAAX")
    (by decide) (step_6_9 M h)
theorem step_6_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaxAxaxAxaxabAAxaaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAA", 1, false⟩ (word "aabxAAxaaXBAAX") (word "aabxBAAxaxAxaxAxaxabAAxaaXBAAX")
    (by decide) (step_6_10 M h)
theorem step_6_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaxAxaxAxaXabAAxaaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxaxAxaxAxa", 0, true⟩ (word "aabxBAAxaxAxaxAxaxabAAxaaXBAAX") (word "aabxBAAxaxAxaxAxaXabAAxaaXBAAX")
    (by decide) (step_6_11 M h)
theorem step_6_13 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaxAxaxAXaXabAAxaaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxaxAxaxA", 0, true⟩ (word "aabxBAAxaxAxaxAxaXabAAxaaXBAAX") (word "aabxBAAxaxAxaxAXaXabAAxaaXBAAX")
    (by decide) (step_6_12 M h)
theorem step_6_14 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaxAxaXAXaXabAAxaaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxaxAxa", 0, true⟩ (word "aabxBAAxaxAxaxAXaXabAAxaaXBAAX") (word "aabxBAAxaxAxaXAXaXabAAxaaXBAAX")
    (by decide) (step_6_13 M h)
theorem step_6_15 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaxAxbXBXaXabAAxaaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxaxAxaXA", 4, false⟩ (word "aabxBAAxaxAxaXAXaXabAAxaaXBAAX") (word "aabxBAAxaxAxbXBXaXabAAxaaXBAAX")
    (by decide) (step_6_14 M h)
theorem step_6_16 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaxAxbXaBXabAAxaaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxaxAxbXBX", 3, true⟩ (word "aabxBAAxaxAxbXBXaXabAAxaaXBAAX") (word "aabxBAAxaxAxbXaBXabAAxaaXBAAX")
    (by decide) (step_6_15 M h)
theorem step_6_17 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaxAxbaaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxaxAxbXaBX", 3, true⟩ (word "aabxBAAxaxAxbXaBXabAAxaaXBAAX") (word "aabxBAAxaxAxbaaXBAAX")
    (by decide) (step_6_16 M h)
theorem step_6_18 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaxbaXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxaxA", 3, false⟩ (word "aabxBAAxaxAxbaaXBAAX") (word "aabxBAAxaxbaXBAAX")
    (by decide) (step_6_17 M h)
theorem step_6_19 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaabXBAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxa", 3, false⟩ (word "aabxBAAxaxbaXBAAX") (word "aabxBAAxaabXBAAX")
    (by decide) (step_6_18 M h)
theorem step_6_20 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabxBAAxaaaXAAAX") = M.one :=
  checked_step M h ⟨word "aabxBAAxaaaXA", 4, true⟩ (word "aabxBAAxaabXBAAX") (word "aabxBAAxaaaXAAAX")
    (by decide) (step_6_19 M h)
theorem step_6_21 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aaaxAAAxaaaXAAAX") = M.one :=
  checked_step M h ⟨word "aa", 4, false⟩ (word "aabxBAAxaaaXAAAX") (word "aaaxAAAxaaaXAAAX")
    (by decide) (step_6_20 M h)
theorem semantic_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_6 = M.one := by
  have endcheck : reduce target_6 = reduce (word "aaaxAAAxaaaXAAAX") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_6_21 M h)
#check semantic_6
-- N3
def cells_7 : List Cell := [
  ⟨word "AAAxaa", 3, false⟩,
  ⟨word "AAAxaaxbAAXaaaBA", 3, true⟩,
  ⟨word "AxAAxaaXAAX", 2, false⟩,
  ⟨word "AxAAxa", 3, false⟩,
  ⟨word "AxAAxaxA", 3, false⟩,
  ⟨word "AxAAxaxAxbXaBX", 3, true⟩,
  ⟨word "AxAAxaxAxbXBX", 3, true⟩,
  ⟨word "AxAAxaxAxaXA", 4, false⟩,
  ⟨word "AxAAxaxAxa", 0, true⟩,
  ⟨word "AxAAxaxAxaxA", 0, true⟩,
  ⟨word "AxAAxaxAxaxAxa", 0, true⟩,
  ⟨word "AxAA", 1, false⟩]
def target_7 : Word := word "AAAxaaabAAAXaaaB"
theorem area_count_7 : cells_7.length = 12 := by decide
theorem step_7_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_7_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxaxAxaxaXa") = M.one :=
  checked_step M h ⟨word "AxAA", 1, false⟩ (word "") (word "AxAAxaxAxaxAxaxaXa")
    (by decide) (step_7_0 M h)
theorem step_7_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxaxAxaXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxaxAxa", 0, true⟩ (word "AxAAxaxAxaxAxaxaXa") (word "AxAAxaxAxaxAxaXaXa")
    (by decide) (step_7_1 M h)
theorem step_7_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxaxAXaXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxaxA", 0, true⟩ (word "AxAAxaxAxaxAxaXaXa") (word "AxAAxaxAxaxAXaXaXa")
    (by decide) (step_7_2 M h)
theorem step_7_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxaXAXaXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxa", 0, true⟩ (word "AxAAxaxAxaxAXaXaXa") (word "AxAAxaxAxaXAXaXaXa")
    (by decide) (step_7_3 M h)
theorem step_7_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxbXBXaXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxaXA", 4, false⟩ (word "AxAAxaxAxaXAXaXaXa") (word "AxAAxaxAxbXBXaXaXa")
    (by decide) (step_7_4 M h)
theorem step_7_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxbXaBXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxbXBX", 3, true⟩ (word "AxAAxaxAxbXBXaXaXa") (word "AxAAxaxAxbXaBXaXa")
    (by decide) (step_7_5 M h)
theorem step_7_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxbXaaBXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxbXaBX", 3, true⟩ (word "AxAAxaxAxbXaBXaXa") (word "AxAAxaxAxbXaaBXa")
    (by decide) (step_7_6 M h)
theorem step_7_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxbAXaaBXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxA", 3, false⟩ (word "AxAAxaxAxbXaaBXa") (word "AxAAxaxbAXaaBXa")
    (by decide) (step_7_7 M h)
theorem step_7_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaabAAXaaBXa") = M.one :=
  checked_step M h ⟨word "AxAAxa", 3, false⟩ (word "AxAAxaxbAXaaBXa") (word "AxAAxaabAAXaaBXa")
    (by decide) (step_7_8 M h)
theorem step_7_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaxbAAXaaBXa") = M.one :=
  checked_step M h ⟨word "AxAAxaaXAAX", 2, false⟩ (word "AxAAxaabAAXaaBXa") (word "AAAxaaxbAAXaaBXa")
    (by decide) (step_7_9 M h)
theorem step_7_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaxbAAXaaaB") = M.one :=
  checked_step M h ⟨word "AAAxaaxbAAXaaaBA", 3, true⟩ (word "AAAxaaxbAAXaaBXa") (word "AAAxaaxbAAXaaaB")
    (by decide) (step_7_10 M h)
theorem step_7_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaabAAAXaaaB") = M.one :=
  checked_step M h ⟨word "AAAxaa", 3, false⟩ (word "AAAxaaxbAAXaaaB") (word "AAAxaaabAAAXaaaB")
    (by decide) (step_7_11 M h)
theorem semantic_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_7 = M.one := by
  have endcheck : reduce target_7 = reduce (word "AAAxaaabAAAXaaaB") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_7_12 M h)
#check semantic_7
#print axioms semantic_7
end WordCertificate
