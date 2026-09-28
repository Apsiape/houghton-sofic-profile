import FreeReduction
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WordCertificate
-- Generated from SHA-256 e87870172a0c66d4c0b15db16ae6a7d93f3b9528e3a34144a4d54632dbecf352
def word (s : String) : Word := s.toList.map fun c =>
  match c with
  | 'a' => .a | 'A' => .A | 'b' => .b | 'B' => .B | 'x' => .x | _ => .X
-- A(2)
def cells_0 : List Cell := [
  ⟨word "", 2, false⟩]
def target_0 : Word := word "xaaxAAXaaXAA"
theorem area_count_0 : cells_0.length = 1 := by decide
theorem step_0_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_0_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaaxAAXaaXAA") = M.one :=
  checked_step M h ⟨word "", 2, false⟩ (word "") (word "xaaxAAXaaXAA")
    (by decide) (step_0_0 M h)
theorem semantic_0 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_0 = M.one := by
  have endcheck : reduce target_0 = reduce (word "xaaxAAXaaXAA") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_0_1 M h)
#check semantic_0
-- E(0)
def cells_1 : List Cell := [
  ⟨word "B", 4, true⟩]
def target_1 : Word := word "xBaXAb"
theorem area_count_1 : cells_1.length = 1 := by decide
theorem step_1_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_1_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xBaXAb") = M.one :=
  checked_step M h ⟨word "B", 4, true⟩ (word "") (word "xBaXAb")
    (by decide) (step_1_0 M h)
theorem semantic_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_1 = M.one := by
  have endcheck : reduce target_1 = reduce (word "xBaXAb") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_1_1 M h)
#check semantic_1
-- U(1)
def cells_2 : List Cell := [
  ⟨word "axAbXB", 4, true⟩]
def target_2 : Word := word "bxBaXA"
theorem area_count_2 : cells_2.length = 1 := by decide
theorem step_2_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_2_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "bxBaXA") = M.one :=
  checked_step M h ⟨word "axAbXB", 4, true⟩ (word "") (word "bxBaXA")
    (by decide) (step_2_0 M h)
theorem semantic_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_2 = M.one := by
  have endcheck : reduce target_2 = reduce (word "bxBaXA") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_2_1 M h)
#check semantic_2
-- E(1)
def cells_3 : List Cell := [
  ⟨word "axBA", 3, false⟩,
  ⟨word "axBAxaaXAAX", 3, true⟩,
  ⟨word "axBaXAA", 2, true⟩,
  ⟨word "aB", 4, true⟩]
def target_3 : Word := word "axABaaXAAb"
theorem area_count_3 : cells_3.length = 4 := by decide
theorem step_3_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_3_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axBaXAbA") = M.one :=
  checked_step M h ⟨word "aB", 4, true⟩ (word "") (word "axBaXAbA")
    (by decide) (step_3_0 M h)
theorem step_3_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axBAxaaXAAXabA") = M.one :=
  checked_step M h ⟨word "axBaXAA", 2, true⟩ (word "axBaXAbA") (word "axBAxaaXAAXabA")
    (by decide) (step_3_1 M h)
theorem step_3_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axBAxaaXAAb") = M.one :=
  checked_step M h ⟨word "axBAxaaXAAX", 3, true⟩ (word "axBAxaaXAAXabA") (word "axBAxaaXAAb")
    (by decide) (step_3_2 M h)
theorem step_3_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axABaaXAAb") = M.one :=
  checked_step M h ⟨word "axBA", 3, false⟩ (word "axBAxaaXAAb") (word "axABaaXAAb")
    (by decide) (step_3_3 M h)
theorem semantic_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_3 = M.one := by
  have endcheck : reduce target_3 = reduce (word "axABaaXAAb") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_3_4 M h)
#check semantic_3
-- U(2)
def cells_4 : List Cell := [
  ⟨word "baxAbXB", 4, true⟩,
  ⟨word "aaxAAbaBA", 3, false⟩,
  ⟨word "aaxAAbaBAxaaXAAX", 3, true⟩,
  ⟨word "aaxAAbaBaXAA", 2, true⟩,
  ⟨word "aaxAAbaXB", 4, true⟩]
def target_4 : Word := word "bbxBBaaXAA"
theorem area_count_4 : cells_4.length = 5 := by decide
theorem step_4_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_4_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aaxAAbaBaXAbxABaaXAA") = M.one :=
  checked_step M h ⟨word "aaxAAbaXB", 4, true⟩ (word "") (word "aaxAAbaBaXAbxABaaXAA")
    (by decide) (step_4_0 M h)
theorem step_4_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aaxAAbaBAxaaXAAXabxABaaXAA") = M.one :=
  checked_step M h ⟨word "aaxAAbaBaXAA", 2, true⟩ (word "aaxAAbaBaXAbxABaaXAA") (word "aaxAAbaBAxaaXAAXabxABaaXAA")
    (by decide) (step_4_1 M h)
theorem step_4_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aaxAAbaBAxaaXAAbaxABaaXAA") = M.one :=
  checked_step M h ⟨word "aaxAAbaBAxaaXAAX", 3, true⟩ (word "aaxAAbaBAxaaXAAXabxABaaXAA") (word "aaxAAbaBAxaaXAAbaxABaaXAA")
    (by decide) (step_4_2 M h)
theorem step_4_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "baxABaaXAA") = M.one :=
  checked_step M h ⟨word "aaxAAbaBA", 3, false⟩ (word "aaxAAbaBAxaaXAAbaxABaaXAA") (word "baxABaaXAA")
    (by decide) (step_4_3 M h)
theorem step_4_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "bbxBBaaXAA") = M.one :=
  checked_step M h ⟨word "baxAbXB", 4, true⟩ (word "baxABaaXAA") (word "bbxBBaaXAA")
    (by decide) (step_4_4 M h)
theorem semantic_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_4 = M.one := by
  have endcheck : reduce target_4 = reduce (word "bbxBBaaXAA") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_4_5 M h)
#check semantic_4
-- B0
def cells_5 : List Cell := [
  ⟨word "xaxAxaXA", 4, false⟩,
  ⟨word "xaxAxa", 0, true⟩,
  ⟨word "xaxAxaxA", 0, true⟩,
  ⟨word "xaxAxaxAxa", 0, true⟩,
  ⟨word "", 1, false⟩]
def target_5 : Word := word "xaxAxbXBXaXA"
theorem area_count_5 : cells_5.length = 5 := by decide
theorem step_5_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_5_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAxaxA") = M.one :=
  checked_step M h ⟨word "", 1, false⟩ (word "") (word "xaxAxaxAxaxA")
    (by decide) (step_5_0 M h)
theorem step_5_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAxaXA") = M.one :=
  checked_step M h ⟨word "xaxAxaxAxa", 0, true⟩ (word "xaxAxaxAxaxA") (word "xaxAxaxAxaXA")
    (by decide) (step_5_1 M h)
theorem step_5_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAXaXA") = M.one :=
  checked_step M h ⟨word "xaxAxaxA", 0, true⟩ (word "xaxAxaxAxaXA") (word "xaxAxaxAXaXA")
    (by decide) (step_5_2 M h)
theorem step_5_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaXAXaXA") = M.one :=
  checked_step M h ⟨word "xaxAxa", 0, true⟩ (word "xaxAxaxAXaXA") (word "xaxAxaXAXaXA")
    (by decide) (step_5_3 M h)
theorem step_5_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxbXBXaXA") = M.one :=
  checked_step M h ⟨word "xaxAxaXA", 4, false⟩ (word "xaxAxaXAXaXA") (word "xaxAxbXBXaXA")
    (by decide) (step_5_4 M h)
theorem semantic_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_5 = M.one := by
  have endcheck : reduce target_5 = reduce (word "xaxAxbXBXaXA") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_5_5 M h)
#check semantic_5
-- B(2)
def cells_6 : List Cell := [
  ⟨word "AAxa", 3, false⟩,
  ⟨word "AAxaxA", 3, false⟩,
  ⟨word "AAxaxAxbXaBX", 3, true⟩,
  ⟨word "AAxaxAxbXBX", 3, true⟩,
  ⟨word "AAxaxAxaXA", 4, false⟩,
  ⟨word "AAxaxAxa", 0, true⟩,
  ⟨word "AAxaxAxaxA", 0, true⟩,
  ⟨word "AAxaxAxaxAxa", 0, true⟩,
  ⟨word "AA", 1, false⟩]
def target_6 : Word := word "AAxaabAAXaaB"
theorem area_count_6 : cells_6.length = 9 := by decide
theorem step_6_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_6_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxaxAxaxa") = M.one :=
  checked_step M h ⟨word "AA", 1, false⟩ (word "") (word "AAxaxAxaxAxaxa")
    (by decide) (step_6_0 M h)
theorem step_6_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxaxAxaXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxaxAxa", 0, true⟩ (word "AAxaxAxaxAxaxa") (word "AAxaxAxaxAxaXa")
    (by decide) (step_6_1 M h)
theorem step_6_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxaxAXaXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxaxA", 0, true⟩ (word "AAxaxAxaxAxaXa") (word "AAxaxAxaxAXaXa")
    (by decide) (step_6_2 M h)
theorem step_6_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxaXAXaXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxa", 0, true⟩ (word "AAxaxAxaxAXaXa") (word "AAxaxAxaXAXaXa")
    (by decide) (step_6_3 M h)
theorem step_6_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxbXBXaXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxaXA", 4, false⟩ (word "AAxaxAxaXAXaXa") (word "AAxaxAxbXBXaXa")
    (by decide) (step_6_4 M h)
theorem step_6_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxbXaBXa") = M.one :=
  checked_step M h ⟨word "AAxaxAxbXBX", 3, true⟩ (word "AAxaxAxbXBXaXa") (word "AAxaxAxbXaBXa")
    (by decide) (step_6_5 M h)
theorem step_6_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxAxbXaaB") = M.one :=
  checked_step M h ⟨word "AAxaxAxbXaBX", 3, true⟩ (word "AAxaxAxbXaBXa") (word "AAxaxAxbXaaB")
    (by decide) (step_6_6 M h)
theorem step_6_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaxbAXaaB") = M.one :=
  checked_step M h ⟨word "AAxaxA", 3, false⟩ (word "AAxaxAxbXaaB") (word "AAxaxbAXaaB")
    (by decide) (step_6_7 M h)
theorem step_6_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAxaabAAXaaB") = M.one :=
  checked_step M h ⟨word "AAxa", 3, false⟩ (word "AAxaxbAXaaB") (word "AAxaabAAXaaB")
    (by decide) (step_6_8 M h)
theorem semantic_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_6 = M.one := by
  have endcheck : reduce target_6 = reduce (word "AAxaabAAXaaB") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_6_9 M h)
#check semantic_6
-- A(3)
def cells_7 : List Cell := [
  ⟨word "xaaaxAbXB", 4, false⟩,
  ⟨word "xaabxBAAXaabXBaxAbXB", 4, true⟩,
  ⟨word "xa", 3, false⟩,
  ⟨word "xaxA", 3, false⟩,
  ⟨word "xaxAxbXaBX", 3, true⟩,
  ⟨word "xaxAxbXBX", 3, true⟩,
  ⟨word "xaxAxaXA", 4, false⟩,
  ⟨word "xaxAxa", 0, true⟩,
  ⟨word "xaxAxaxA", 0, true⟩,
  ⟨word "xaxAxaxAxa", 0, true⟩,
  ⟨word "", 1, false⟩,
  ⟨word "aabAAxaaxAAXaaBAA", 1, true⟩,
  ⟨word "aabAAxaaxAAXaaBAAxaxAxaxAxa", 0, false⟩,
  ⟨word "aabAAxaaxAAXaaBAAxaxAxaxA", 0, false⟩,
  ⟨word "aabAAxaaxAAXaaBAAxaxAxa", 0, false⟩,
  ⟨word "aabAAxaaxAAXaaBAAxaxAxaXA", 4, true⟩,
  ⟨word "aabAAxaaxAAXaaBAAxaxAxbXBX", 3, false⟩,
  ⟨word "aabAAxaaxAAXaaBAAxaxAxbXaBX", 3, false⟩,
  ⟨word "aabAAxaaxAAXaaBAAxaxA", 3, true⟩,
  ⟨word "aabAAxaaxAAXaaBAAxa", 3, true⟩,
  ⟨word "aabxAAxaaXAAX", 2, false⟩]
def target_7 : Word := word "xaaaxAAAXaaaXAAA"
theorem area_count_7 : cells_7.length = 21 := by decide
theorem step_7_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_7_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaXBAA") = M.one :=
  checked_step M h ⟨word "aabxAAxaaXAAX", 2, false⟩ (word "") (word "aabAAxaaxAAXaaXBAA")
    (by decide) (step_7_0 M h)
theorem step_7_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaBAAxaxbaBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAAxa", 3, true⟩ (word "aabAAxaaxAAXaaXBAA") (word "aabAAxaaxAAXaaBAAxaxbaBAAXaabXBAA")
    (by decide) (step_7_1 M h)
theorem step_7_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaBAAxaxAxbaaBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAAxaxA", 3, true⟩ (word "aabAAxaaxAAXaaBAAxaxbaBAAXaabXBAA") (word "aabAAxaaxAAXaaBAAxaxAxbaaBAAXaabXBAA")
    (by decide) (step_7_2 M h)
theorem step_7_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaBAAxaxAxbXaBXabAAxaaBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAAxaxAxbXaBX", 3, false⟩ (word "aabAAxaaxAAXaaBAAxaxAxbaaBAAXaabXBAA") (word "aabAAxaaxAAXaaBAAxaxAxbXaBXabAAxaaBAAXaabXBAA")
    (by decide) (step_7_3 M h)
theorem step_7_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaBAAxaxAxbXBXaXabAAxaaBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAAxaxAxbXBX", 3, false⟩ (word "aabAAxaaxAAXaaBAAxaxAxbXaBXabAAxaaBAAXaabXBAA") (word "aabAAxaaxAAXaaBAAxaxAxbXBXaXabAAxaaBAAXaabXBAA")
    (by decide) (step_7_4 M h)
theorem step_7_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaBAAxaxAxaXAXaXabAAxaaBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAAxaxAxaXA", 4, true⟩ (word "aabAAxaaxAAXaaBAAxaxAxbXBXaXabAAxaaBAAXaabXBAA") (word "aabAAxaaxAAXaaBAAxaxAxaXAXaXabAAxaaBAAXaabXBAA")
    (by decide) (step_7_5 M h)
theorem step_7_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaBAAxaxAxaxAXaXabAAxaaBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAAxaxAxa", 0, false⟩ (word "aabAAxaaxAAXaaBAAxaxAxaXAXaXabAAxaaBAAXaabXBAA") (word "aabAAxaaxAAXaaBAAxaxAxaxAXaXabAAxaaBAAXaabXBAA")
    (by decide) (step_7_6 M h)
theorem step_7_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaBAAxaxAxaxAxaXabAAxaaBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAAxaxAxaxA", 0, false⟩ (word "aabAAxaaxAAXaaBAAxaxAxaxAXaXabAAxaaBAAXaabXBAA") (word "aabAAxaaxAAXaaBAAxaxAxaxAxaXabAAxaaBAAXaabXBAA")
    (by decide) (step_7_7 M h)
theorem step_7_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxAAXaaBAAxaxAxaxAxaxabAAxaaBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAAxaxAxaxAxa", 0, false⟩ (word "aabAAxaaxAAXaaBAAxaxAxaxAxaXabAAxaaBAAXaabXBAA") (word "aabAAxaaxAAXaaBAAxaxAxaxAxaxabAAxaaBAAXaabXBAA")
    (by decide) (step_7_8 M h)
theorem step_7_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabAAxaaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "aabAAxaaxAAXaaBAA", 1, true⟩ (word "aabAAxaaxAAXaaBAAxaxAxaxAxaxabAAxaaBAAXaabXBAA") (word "aabAAxaaxBAAXaabXBAA")
    (by decide) (step_7_9 M h)
theorem step_7_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAxaxabAAxaaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "", 1, false⟩ (word "aabAAxaaxBAAXaabXBAA") (word "xaxAxaxAxaxabAAxaaxBAAXaabXBAA")
    (by decide) (step_7_10 M h)
theorem step_7_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAxaXabAAxaaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "xaxAxaxAxa", 0, true⟩ (word "xaxAxaxAxaxabAAxaaxBAAXaabXBAA") (word "xaxAxaxAxaXabAAxaaxBAAXaabXBAA")
    (by decide) (step_7_11 M h)
theorem step_7_13 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaxAXaXabAAxaaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "xaxAxaxA", 0, true⟩ (word "xaxAxaxAxaXabAAxaaxBAAXaabXBAA") (word "xaxAxaxAXaXabAAxaaxBAAXaabXBAA")
    (by decide) (step_7_12 M h)
theorem step_7_14 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxaXAXaXabAAxaaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "xaxAxa", 0, true⟩ (word "xaxAxaxAXaXabAAxaaxBAAXaabXBAA") (word "xaxAxaXAXaXabAAxaaxBAAXaabXBAA")
    (by decide) (step_7_13 M h)
theorem step_7_15 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxbXBXaXabAAxaaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "xaxAxaXA", 4, false⟩ (word "xaxAxaXAXaXabAAxaaxBAAXaabXBAA") (word "xaxAxbXBXaXabAAxaaxBAAXaabXBAA")
    (by decide) (step_7_14 M h)
theorem step_7_16 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxbXaBXabAAxaaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "xaxAxbXBX", 3, true⟩ (word "xaxAxbXBXaXabAAxaaxBAAXaabXBAA") (word "xaxAxbXaBXabAAxaaxBAAXaabXBAA")
    (by decide) (step_7_15 M h)
theorem step_7_17 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxAxbaaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "xaxAxbXaBX", 3, true⟩ (word "xaxAxbXaBXabAAxaaxBAAXaabXBAA") (word "xaxAxbaaxBAAXaabXBAA")
    (by decide) (step_7_16 M h)
theorem step_7_18 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaxbaxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "xaxA", 3, false⟩ (word "xaxAxbaaxBAAXaabXBAA") (word "xaxbaxBAAXaabXBAA")
    (by decide) (step_7_17 M h)
theorem step_7_19 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaabxBAAXaabXBAA") = M.one :=
  checked_step M h ⟨word "xa", 3, false⟩ (word "xaxbaxBAAXaabXBAA") (word "xaabxBAAXaabXBAA")
    (by decide) (step_7_18 M h)
theorem step_7_20 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaabxBAAXaaaXAAA") = M.one :=
  checked_step M h ⟨word "xaabxBAAXaabXBaxAbXB", 4, true⟩ (word "xaabxBAAXaabXBAA") (word "xaabxBAAXaaaXAAA")
    (by decide) (step_7_19 M h)
theorem step_7_21 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xaaaxAAAXaaaXAAA") = M.one :=
  checked_step M h ⟨word "xaaaxAbXB", 4, false⟩ (word "xaabxBAAXaaaXAAA") (word "xaaaxAAAXaaaXAAA")
    (by decide) (step_7_20 M h)
theorem semantic_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_7 = M.one := by
  have endcheck : reduce target_7 = reduce (word "xaaaxAAAXaaaXAAA") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_7_21 M h)
#check semantic_7
-- B(3)
def cells_8 : List Cell := [
  ⟨word "AAAxaa", 3, false⟩,
  ⟨word "AAAxaaxA", 3, false⟩,
  ⟨word "AAAxaaxAxA", 3, false⟩,
  ⟨word "AAAxaaxAxAxbXaaBX", 3, true⟩,
  ⟨word "AAAxaaxAxAxbXaBX", 3, true⟩,
  ⟨word "AAAxaaxAxAxbXBX", 3, true⟩,
  ⟨word "AAA", 2, false⟩,
  ⟨word "AxAAxaxAxaXA", 4, false⟩,
  ⟨word "AxAAxaxAxa", 0, true⟩,
  ⟨word "AxAAxaxAxaxA", 0, true⟩,
  ⟨word "AxAAxaxAxaxAxa", 0, true⟩,
  ⟨word "AxAA", 1, false⟩]
def target_8 : Word := word "AAAxaaabAAAXaaaB"
theorem area_count_8 : cells_8.length = 12 := by decide
theorem step_8_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_8_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxaxAxaxaXa") = M.one :=
  checked_step M h ⟨word "AxAA", 1, false⟩ (word "") (word "AxAAxaxAxaxAxaxaXa")
    (by decide) (step_8_0 M h)
theorem step_8_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxaxAxaXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxaxAxa", 0, true⟩ (word "AxAAxaxAxaxAxaxaXa") (word "AxAAxaxAxaxAxaXaXa")
    (by decide) (step_8_1 M h)
theorem step_8_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxaxAXaXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxaxA", 0, true⟩ (word "AxAAxaxAxaxAxaXaXa") (word "AxAAxaxAxaxAXaXaXa")
    (by decide) (step_8_2 M h)
theorem step_8_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxaXAXaXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxa", 0, true⟩ (word "AxAAxaxAxaxAXaXaXa") (word "AxAAxaxAxaXAXaXaXa")
    (by decide) (step_8_3 M h)
theorem step_8_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AxAAxaxAxbXBXaXaXa") = M.one :=
  checked_step M h ⟨word "AxAAxaxAxaXA", 4, false⟩ (word "AxAAxaxAxaXAXaXaXa") (word "AxAAxaxAxbXBXaXaXa")
    (by decide) (step_8_4 M h)
theorem step_8_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaxAxAxbXBXaXaXa") = M.one :=
  checked_step M h ⟨word "AAA", 2, false⟩ (word "AxAAxaxAxbXBXaXaXa") (word "AAAxaaxAxAxbXBXaXaXa")
    (by decide) (step_8_5 M h)
theorem step_8_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaxAxAxbXaBXaXa") = M.one :=
  checked_step M h ⟨word "AAAxaaxAxAxbXBX", 3, true⟩ (word "AAAxaaxAxAxbXBXaXaXa") (word "AAAxaaxAxAxbXaBXaXa")
    (by decide) (step_8_6 M h)
theorem step_8_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaxAxAxbXaaBXa") = M.one :=
  checked_step M h ⟨word "AAAxaaxAxAxbXaBX", 3, true⟩ (word "AAAxaaxAxAxbXaBXaXa") (word "AAAxaaxAxAxbXaaBXa")
    (by decide) (step_8_7 M h)
theorem step_8_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaxAxAxbXaaaB") = M.one :=
  checked_step M h ⟨word "AAAxaaxAxAxbXaaBX", 3, true⟩ (word "AAAxaaxAxAxbXaaBXa") (word "AAAxaaxAxAxbXaaaB")
    (by decide) (step_8_8 M h)
theorem step_8_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaxAxbAXaaaB") = M.one :=
  checked_step M h ⟨word "AAAxaaxAxA", 3, false⟩ (word "AAAxaaxAxAxbXaaaB") (word "AAAxaaxAxbAXaaaB")
    (by decide) (step_8_9 M h)
theorem step_8_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaxbAAXaaaB") = M.one :=
  checked_step M h ⟨word "AAAxaaxA", 3, false⟩ (word "AAAxaaxAxbAXaaaB") (word "AAAxaaxbAAXaaaB")
    (by decide) (step_8_10 M h)
theorem step_8_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "AAAxaaabAAAXaaaB") = M.one :=
  checked_step M h ⟨word "AAAxaa", 3, false⟩ (word "AAAxaaxbAAXaaaB") (word "AAAxaaabAAAXaaaB")
    (by decide) (step_8_11 M h)
theorem semantic_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_8 = M.one := by
  have endcheck : reduce target_8 = reduce (word "AAAxaaabAAAXaaaB") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_8_12 M h)
#check semantic_8
-- N4
def cells_9 : List Cell := [
  ⟨word "BAB", 3, false⟩,
  ⟨word "BABxbaBX", 3, true⟩,
  ⟨word "BABxbaBXbbABX", 3, true⟩,
  ⟨word "BABxbaBXbbABXbaBBX", 3, true⟩,
  ⟨word "BAB", 3, true⟩,
  ⟨word "BABaXbbABXX", 3, true⟩,
  ⟨word "BABaXbbABXXBX", 3, true⟩,
  ⟨word "BABaXA", 3, false⟩,
  ⟨word "BABaXAxb", 3, false⟩,
  ⟨word "BABaXAxbXBXaXA", 3, false⟩,
  ⟨word "BABaXAxaXA", 4, false⟩,
  ⟨word "BABaXA", 0, false⟩,
  ⟨word "BABaXAXaXAXaXA", 0, false⟩,
  ⟨word "BAB", 1, true⟩]
def target_9 : Word := word "BABabbBaBAbaAbBAbaBaBAbaAb"
theorem area_count_9 : cells_9.length = 14 := by decide
theorem step_9_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_9_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXAXaXAXaXAXbab") = M.one :=
  checked_step M h ⟨word "BAB", 1, true⟩ (word "") (word "BABaXAXaXAXaXAXbab")
    (by decide) (step_9_0 M h)
theorem step_9_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXAXaXAXaXAxbab") = M.one :=
  checked_step M h ⟨word "BABaXAXaXAXaXA", 0, false⟩ (word "BABaXAXaXAXaXAXbab") (word "BABaXAXaXAXaXAxbab")
    (by decide) (step_9_1 M h)
theorem step_9_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXAxaXAXaXAxbab") = M.one :=
  checked_step M h ⟨word "BABaXA", 0, false⟩ (word "BABaXAXaXAXaXAxbab") (word "BABaXAxaXAXaXAxbab")
    (by decide) (step_9_2 M h)
theorem step_9_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXAxbXBXaXAxbab") = M.one :=
  checked_step M h ⟨word "BABaXAxaXA", 4, false⟩ (word "BABaXAxaXAXaXAxbab") (word "BABaXAxbXBXaXAxbab")
    (by decide) (step_9_3 M h)
theorem step_9_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXAxbXBXaXbb") = M.one :=
  checked_step M h ⟨word "BABaXAxbXBXaXA", 3, false⟩ (word "BABaXAxbXBXaXAxbab") (word "BABaXAxbXBXaXbb")
    (by decide) (step_9_4 M h)
theorem step_9_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXAxbabABXXBXaXbb") = M.one :=
  checked_step M h ⟨word "BABaXAxb", 3, false⟩ (word "BABaXAxbXBXaXbb") (word "BABaXAxbabABXXBXaXbb")
    (by decide) (step_9_5 M h)
theorem step_9_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXbbABXXBXaXbb") = M.one :=
  checked_step M h ⟨word "BABaXA", 3, false⟩ (word "BABaXAxbabABXXBXaXbb") (word "BABaXbbABXXBXaXbb")
    (by decide) (step_9_6 M h)
theorem step_9_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXbbABXXaBXbb") = M.one :=
  checked_step M h ⟨word "BABaXbbABXXBX", 3, true⟩ (word "BABaXbbABXXBXaXbb") (word "BABaXbbABXXaBXbb")
    (by decide) (step_9_7 M h)
theorem step_9_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABaXbbABXbaBBXbb") = M.one :=
  checked_step M h ⟨word "BABaXbbABXX", 3, true⟩ (word "BABaXbbABXXaBXbb") (word "BABaXbbABXbaBBXbb")
    (by decide) (step_9_8 M h)
theorem step_9_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABxbaBXbbABXbaBBXbb") = M.one :=
  checked_step M h ⟨word "BAB", 3, true⟩ (word "BABaXbbABXbaBBXbb") (word "BABxbaBXbbABXbaBBXbb")
    (by decide) (step_9_9 M h)
theorem step_9_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABxbaBXbbABXbaBaBAbb") = M.one :=
  checked_step M h ⟨word "BABxbaBXbbABXbaBBX", 3, true⟩ (word "BABxbaBXbbABXbaBBXbb") (word "BABxbaBXbbABXbaBaBAbb")
    (by decide) (step_9_10 M h)
theorem step_9_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABxbaBXbAbaBaBAbb") = M.one :=
  checked_step M h ⟨word "BABxbaBXbbABX", 3, true⟩ (word "BABxbaBXbbABXbaBaBAbb") (word "BABxbaBXbAbaBaBAbb")
    (by decide) (step_9_11 M h)
theorem step_9_13 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABxbaaBAbAbaBaBAbb") = M.one :=
  checked_step M h ⟨word "BABxbaBX", 3, true⟩ (word "BABxbaBXbAbaBaBAbb") (word "BABxbaaBAbAbaBaBAbb")
    (by decide) (step_9_12 M h)
theorem step_9_14 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "BABabaBAbAbaBaBAbb") = M.one :=
  checked_step M h ⟨word "BAB", 3, false⟩ (word "BABxbaaBAbAbaBaBAbb") (word "BABabaBAbAbaBaBAbb")
    (by decide) (step_9_13 M h)
theorem semantic_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_9 = M.one := by
  have endcheck : reduce target_9 = reduce (word "BABabaBAbAbaBaBAbb") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_9_14 M h)
#check semantic_9
-- [x,rho]
def cells_10 : List Cell := [
  ⟨word "xABaaXA", 4, false⟩,
  ⟨word "xBA", 3, false⟩,
  ⟨word "xBAxaaXAAX", 3, true⟩,
  ⟨word "xBaXAA", 2, true⟩,
  ⟨word "B", 4, true⟩]
def target_10 : Word := word "xABabXBAba"
theorem area_count_10 : cells_10.length = 5 := by decide
theorem step_10_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_10_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xBaXAb") = M.one :=
  checked_step M h ⟨word "B", 4, true⟩ (word "") (word "xBaXAb")
    (by decide) (step_10_0 M h)
theorem step_10_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xBAxaaXAAXab") = M.one :=
  checked_step M h ⟨word "xBaXAA", 2, true⟩ (word "xBaXAb") (word "xBAxaaXAAXab")
    (by decide) (step_10_1 M h)
theorem step_10_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xBAxaaXAAba") = M.one :=
  checked_step M h ⟨word "xBAxaaXAAX", 3, true⟩ (word "xBAxaaXAAXab") (word "xBAxaaXAAba")
    (by decide) (step_10_2 M h)
theorem step_10_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xABaaXAAba") = M.one :=
  checked_step M h ⟨word "xBA", 3, false⟩ (word "xBAxaaXAAba") (word "xABaaXAAba")
    (by decide) (step_10_3 M h)
theorem step_10_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "xABabXBAba") = M.one :=
  checked_step M h ⟨word "xABaaXA", 4, false⟩ (word "xABaaXAAba") (word "xABabXBAba")
    (by decide) (step_10_4 M h)
theorem semantic_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_10 = M.one := by
  have endcheck : reduce target_10 = reduce (word "xABabXBAba") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_10_5 M h)
#check semantic_10
-- CONV
def cells_11 : List Cell := [
  ⟨word "a", 3, false⟩,
  ⟨word "axb", 3, false⟩,
  ⟨word "axbxBA", 3, false⟩,
  ⟨word "axbxBAxb", 3, false⟩,
  ⟨word "axbxBAx", 4, true⟩,
  ⟨word "ax", 4, true⟩]
def target_11 : Word := word "aabbAABBaXAXaaXAAaXA"
theorem area_count_11 : cells_11.length = 6 := by decide
theorem step_11_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_11_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBaXAXA") = M.one :=
  checked_step M h ⟨word "ax", 4, true⟩ (word "") (word "axbxBaXAXA")
    (by decide) (step_11_0 M h)
theorem step_11_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBAxbxBaXAXaaXAXA") = M.one :=
  checked_step M h ⟨word "axbxBAx", 4, true⟩ (word "axbxBaXAXA") (word "axbxBAxbxBaXAXaaXAXA")
    (by decide) (step_11_1 M h)
theorem step_11_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBAxbabABBaXAXaaXAXA") = M.one :=
  checked_step M h ⟨word "axbxBAxb", 3, false⟩ (word "axbxBAxbxBaXAXaaXAXA") (word "axbxBAxbabABBaXAXaaXAXA")
    (by decide) (step_11_2 M h)
theorem step_11_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxbABBaXAXaaXAXA") = M.one :=
  checked_step M h ⟨word "axbxBA", 3, false⟩ (word "axbxBAxbabABBaXAXaaXAXA") (word "axbxbABBaXAXaaXAXA")
    (by decide) (step_11_3 M h)
theorem step_11_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbabAABBaXAXaaXAXA") = M.one :=
  checked_step M h ⟨word "axb", 3, false⟩ (word "axbxbABBaXAXaaXAXA") (word "axbabAABBaXAXaaXAXA")
    (by decide) (step_11_4 M h)
theorem step_11_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabbAABBaXAXaaXAXA") = M.one :=
  checked_step M h ⟨word "a", 3, false⟩ (word "axbabAABBaXAXaaXAXA") (word "aabbAABBaXAXaaXAXA")
    (by decide) (step_11_5 M h)
theorem semantic_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_11 = M.one := by
  have endcheck : reduce target_11 = reduce (word "aabbAABBaXAXaaXAXA") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_11_6 M h)
#check semantic_11
-- BRAID
def cells_12 : List Cell := [
  ⟨word "axAxaxA", 0, true⟩,
  ⟨word "axAxaxAxa", 0, true⟩,
  ⟨word "axAxaxAxaxA", 0, true⟩,
  ⟨word "X", 1, false⟩]
def target_12 : Word := word "axAxaxAXaXAX"
theorem area_count_12 : cells_12.length = 4 := by decide
theorem step_12_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_12_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaxAxaxAx") = M.one :=
  checked_step M h ⟨word "X", 1, false⟩ (word "") (word "axAxaxAxaxAx")
    (by decide) (step_12_0 M h)
theorem step_12_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaxAxaxAX") = M.one :=
  checked_step M h ⟨word "axAxaxAxaxA", 0, true⟩ (word "axAxaxAxaxAx") (word "axAxaxAxaxAX")
    (by decide) (step_12_1 M h)
theorem step_12_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaxAxaXAX") = M.one :=
  checked_step M h ⟨word "axAxaxAxa", 0, true⟩ (word "axAxaxAxaxAX") (word "axAxaxAxaXAX")
    (by decide) (step_12_2 M h)
theorem step_12_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxaxAXaXAX") = M.one :=
  checked_step M h ⟨word "axAxaxA", 0, true⟩ (word "axAxaxAxaXAX") (word "axAxaxAXaXAX")
    (by decide) (step_12_3 M h)
theorem semantic_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_12 = M.one := by
  have endcheck : reduce target_12 = reduce (word "axAxaxAXaXAX") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_12_4 M h)
#check semantic_12
-- psi(r1)
def cells_13 : List Cell := [
  ⟨word "a", 3, false⟩,
  ⟨word "axb", 3, false⟩,
  ⟨word "axbxBA", 3, false⟩,
  ⟨word "axbxBAxb", 3, false⟩,
  ⟨word "axbxBAx", 4, true⟩,
  ⟨word "ax", 4, true⟩,
  ⟨word "axaxAAxax", 3, false⟩,
  ⟨word "axaxAAxaxxb", 3, false⟩,
  ⟨word "axaxAAxaxxbxBA", 3, false⟩,
  ⟨word "axaxAAxaxxbxBAxb", 3, false⟩,
  ⟨word "axaxAAxaxxbxBAx", 4, true⟩,
  ⟨word "axaxAAxaxx", 4, true⟩,
  ⟨word "axaxAAxa", 0, false⟩,
  ⟨word "axaxAA", 2, false⟩,
  ⟨word "axa", 0, false⟩,
  ⟨word "axA", 0, false⟩,
  ⟨word "a", 0, false⟩]
def target_13 : Word := word "aabbAABBaabbAABB"
theorem area_count_13 : cells_13.length = 17 := by decide
theorem step_13_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem step_13_1 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axxA") = M.one :=
  checked_step M h ⟨word "a", 0, false⟩ (word "") (word "axxA")
    (by decide) (step_13_0 M h)
theorem step_13_2 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axAxxaxA") = M.one :=
  checked_step M h ⟨word "axA", 0, false⟩ (word "axxA") (word "axAxxaxA")
    (by decide) (step_13_1 M h)
theorem step_13_3 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxxAAxxaxA") = M.one :=
  checked_step M h ⟨word "axa", 0, false⟩ (word "axAxxaxA") (word "axaxxAAxxaxA")
    (by decide) (step_13_2 M h)
theorem step_13_4 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaaxAAxaxA") = M.one :=
  checked_step M h ⟨word "axaxAA", 2, false⟩ (word "axaxxAAxxaxA") (word "axaxAAxaaxAAxaxA")
    (by decide) (step_13_3 M h)
theorem step_13_5 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaxxaxAAxaxA") = M.one :=
  checked_step M h ⟨word "axaxAAxa", 0, false⟩ (word "axaxAAxaaxAAxaxA") (word "axaxAAxaxxaxAAxaxA")
    (by decide) (step_13_4 M h)
theorem step_13_6 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaxxbxBAxaxA") = M.one :=
  checked_step M h ⟨word "axaxAAxaxx", 4, true⟩ (word "axaxAAxaxxaxAAxaxA") (word "axaxAAxaxxbxBAxaxA")
    (by decide) (step_13_5 M h)
theorem step_13_7 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaxxbxBAxbxB") = M.one :=
  checked_step M h ⟨word "axaxAAxaxxbxBAx", 4, true⟩ (word "axaxAAxaxxbxBAxaxA") (word "axaxAAxaxxbxBAxbxB")
    (by decide) (step_13_6 M h)
theorem step_13_8 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaxxbxBAxbabABB") = M.one :=
  checked_step M h ⟨word "axaxAAxaxxbxBAxb", 3, false⟩ (word "axaxAAxaxxbxBAxbxB") (word "axaxAAxaxxbxBAxbabABB")
    (by decide) (step_13_7 M h)
theorem step_13_9 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaxxbxbABB") = M.one :=
  checked_step M h ⟨word "axaxAAxaxxbxBA", 3, false⟩ (word "axaxAAxaxxbxBAxbabABB") (word "axaxAAxaxxbxbABB")
    (by decide) (step_13_8 M h)
theorem step_13_10 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaxxbabAABB") = M.one :=
  checked_step M h ⟨word "axaxAAxaxxb", 3, false⟩ (word "axaxAAxaxxbxbABB") (word "axaxAAxaxxbabAABB")
    (by decide) (step_13_9 M h)
theorem step_13_11 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axaxAAxaxabbAABB") = M.one :=
  checked_step M h ⟨word "axaxAAxax", 3, false⟩ (word "axaxAAxaxxbabAABB") (word "axaxAAxaxabbAABB")
    (by decide) (step_13_10 M h)
theorem step_13_12 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBAxaxabbAABB") = M.one :=
  checked_step M h ⟨word "ax", 4, true⟩ (word "axaxAAxaxabbAABB") (word "axbxBAxaxabbAABB")
    (by decide) (step_13_11 M h)
theorem step_13_13 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBAxbxBaabbAABB") = M.one :=
  checked_step M h ⟨word "axbxBAx", 4, true⟩ (word "axbxBAxaxabbAABB") (word "axbxBAxbxBaabbAABB")
    (by decide) (step_13_12 M h)
theorem step_13_14 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxBAxbabABBaabbAABB") = M.one :=
  checked_step M h ⟨word "axbxBAxb", 3, false⟩ (word "axbxBAxbxBaabbAABB") (word "axbxBAxbabABBaabbAABB")
    (by decide) (step_13_13 M h)
theorem step_13_15 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbxbABBaabbAABB") = M.one :=
  checked_step M h ⟨word "axbxBA", 3, false⟩ (word "axbxBAxbabABBaabbAABB") (word "axbxbABBaabbAABB")
    (by decide) (step_13_14 M h)
theorem step_13_16 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "axbabAABBaabbAABB") = M.one :=
  checked_step M h ⟨word "axb", 3, false⟩ (word "axbxbABBaabbAABB") (word "axbabAABBaabbAABB")
    (by decide) (step_13_15 M h)
theorem step_13_17 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "aabbAABBaabbAABB") = M.one :=
  checked_step M h ⟨word "a", 3, false⟩ (word "axbabAABBaabbAABB") (word "aabbAABBaabbAABB")
    (by decide) (step_13_16 M h)
theorem semantic_13 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_13 = M.one := by
  have endcheck : reduce target_13 = reduce (word "aabbAABBaabbAABB") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_13_17 M h)
#check semantic_13
-- psi(r4)
def cells_14 : List Cell := [
]
def target_14 : Word := word "aabbAABBbbaaBBAA"
theorem area_count_14 : cells_14.length = 0 := by decide
theorem step_14_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :
    eval M (word "") = M.one := rfl
theorem semantic_14 (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :
    eval M target_14 = M.one := by
  have endcheck : reduce target_14 = reduce (word "") := by decide
  exact (reduction_equality_sound M _ _ endcheck).trans (step_14_0 M h)
#check semantic_14
#print axioms semantic_14
end WordCertificate
