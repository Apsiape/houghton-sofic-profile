import Houghton
set_option autoImplicit false
set_option maxRecDepth 100000

namespace PaperStatements

section
/-- Theorem 3.1. Original: `Houghton.astar_le_pow`. -/
def theorem_3_1 : Prop :=
  ∀ (M : Nat) (hM : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) M),
  Houghton.AstarLE M
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) M
      (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
end

section
/-- Theorem 3.2. Original: `Houghton.astar_le_weighted_rpow`. -/
def theorem_3_2 : Prop :=
  ∀ (M : Nat) (hM : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M),
  @Exists.{1} Nat fun (n : Nat) =>
    And (Houghton.AstarLE M n)
      (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast n)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 135)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 135) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 134) (instOfNatNat (nat_lit 134)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 133) (instOfNatNat (nat_lit 133)))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast M)
            (Real.logb
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 107)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 107) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 105) (instOfNatNat (nat_lit 105)))))))))))
end

section
/-- Theorem 3.3. Original: `Houghton.dehn_bound`. -/
def theorem_3_3 : Prop :=
  ∀ (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
  (w : Houghton.F)
  (hw :
    @LE.le.{0} Nat instLENat
      (@List.length.{0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Bool)
        (@FreeGroup.toWord.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) w))
      n)
  (h1 :
    @Eq.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
      (@DFunLike.coe.{1, 1, 1}
        (@MonoidHom.{0, 0} Houghton.F (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@MulOneClass.toMulOne.{0} Houghton.F
            (@Monoid.toMulOneClass.{0} Houghton.F
              (@DivInvMonoid.toMonoid.{0} Houghton.F
                (@Group.toDivInvMonoid.{0} Houghton.F
                  (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
          (@MulOpposite.instMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
            (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
              (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                  (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))))))
        Houghton.F (fun (x : Houghton.F) => MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
        (@MonoidHom.instFunLike.{0, 0} Houghton.F (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@MulOneClass.toMulOne.{0} Houghton.F
            (@Monoid.toMulOneClass.{0} Houghton.F
              (@DivInvMonoid.toMonoid.{0} Houghton.F
                (@Group.toDivInvMonoid.{0} Houghton.F
                  (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
          (@MulOpposite.instMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
            (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
              (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                  (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))))))
        Houghton.ρH w)
      (@OfNat.ofNat.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) (nat_lit 1)
        (@One.toOfNat1.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@MulOpposite.instOne.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.instOne.{0} Houghton.Y)))))
  (A : Nat)
  (hA :
    Houghton.AstarLE
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      A),
  Houghton.AreaLE w
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 400) (instOfNatNat (nat_lit 400)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) A))
end

section
/-- Theorem 3.3, polynomial consequence. Original: `Houghton.dehn_poly_weighted`. -/
def theorem_3_3_polynomial : Prop :=
  @Exists.{1} Real fun (C : Real) =>
  ∀ (n : Nat),
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
      ∀ (w : Houghton.F),
        @LE.le.{0} Nat instLENat
            (@List.length.{0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Bool)
              (@FreeGroup.toWord.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) w))
            n →
          @Eq.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@DFunLike.coe.{1, 1, 1}
                (@MonoidHom.{0, 0} Houghton.F (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOneClass.toMulOne.{0} Houghton.F
                    (@Monoid.toMulOneClass.{0} Houghton.F
                      (@DivInvMonoid.toMonoid.{0} Houghton.F
                        (@Group.toDivInvMonoid.{0} Houghton.F
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
                  (@MulOpposite.instMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                            (@Equiv.Perm.permGroup.{0} Houghton.Y)))))))
                Houghton.F (fun (x : Houghton.F) => MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MonoidHom.instFunLike.{0, 0} Houghton.F (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOneClass.toMulOne.{0} Houghton.F
                    (@Monoid.toMulOneClass.{0} Houghton.F
                      (@DivInvMonoid.toMonoid.{0} Houghton.F
                        (@Group.toDivInvMonoid.{0} Houghton.F
                          (@FreeGroup.instGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
                  (@MulOpposite.instMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                    (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
                      (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                        (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                          (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                            (@Equiv.Perm.permGroup.{0} Houghton.Y)))))))
                Houghton.ρH w)
              (@OfNat.ofNat.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) (nat_lit 1)
                (@One.toOfNat1.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOpposite.instOne.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.instOne.{0} Houghton.Y)))) →
            Houghton.AreaLE w
              (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                  (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (@Nat.cast.{0} Real Real.instNatCast n)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (Real.logb
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (@OfNat.ofNat.{0} Real (nat_lit 107)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 107) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 105) (instOfNatNat (nat_lit 105))))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
end

section
/-- Johnson presentation. Original: `Houghton.null_iff_areaLE`. -/
def johnson_presentation : Prop :=
  ∀ (w : Houghton.F),
  Iff
    (@Eq.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
      (@DFunLike.coe.{1, 1, 1}
        (@MonoidHom.{0, 0} Houghton.F (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@MulOneClass.toMulOne.{0} Houghton.F
            (@Monoid.toMulOneClass.{0} Houghton.F
              (@DivInvMonoid.toMonoid.{0} Houghton.F
                (@Group.toDivInvMonoid.{0} Houghton.F
                  (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
          (@MulOpposite.instMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
            (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
              (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                  (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))))))
        Houghton.F (fun (x : Houghton.F) => MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
        (@MonoidHom.instFunLike.{0, 0} Houghton.F (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@MulOneClass.toMulOne.{0} Houghton.F
            (@Monoid.toMulOneClass.{0} Houghton.F
              (@DivInvMonoid.toMonoid.{0} Houghton.F
                (@Group.toDivInvMonoid.{0} Houghton.F
                  (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
          (@MulOpposite.instMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
            (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Houghton.Y)
              (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
                (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                  (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))))))
        Houghton.ρH w)
      (@OfNat.ofNat.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) (nat_lit 1)
        (@One.toOfNat1.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@MulOpposite.instOne.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.instOne.{0} Houghton.Y)))))
    (@Exists.{1} Nat fun (n : Nat) => Houghton.AreaLE w n)
end

section
universe u_1
/-- Lemma 2.1, embedding. Original: `Houghton.embeds_of_profile_lt`. -/
def lemma_2_1_embedding : Prop :=
  ∀ {G : Type u_1} [inst : Group.{u_1} G] (E : Finset.{u_1} G) (r : Real)
  (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
  (n : Nat) (hn : @Eq.{1} ENat (@Houghton.profile.{u_1} G inst E r) (@Nat.cast.{0} ENat ENat.instNatCast n))
  (h2 :
    @LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast n)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        r)),
  @Houghton.EmbedsInFiniteGroup.{u_1} G inst E
end

section
universe u_1
/-- Lemma 2.1, dichotomy. Original: `Houghton.profile_bounded_or_ge`. -/
def lemma_2_1_dichotomy : Prop :=
  ∀ {G : Type u_1} [inst : Group.{u_1} G] (E : Finset.{u_1} G),
  Or
    (@Exists.{1} Nat fun (C : Nat) =>
      ∀ (r : Real),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r →
          @LE.le.{0} ENat instLEENat (@Houghton.profile.{u_1} G inst E r) (@Nat.cast.{0} ENat ENat.instNatCast C))
    (∀ (r : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r →
        ∀ (n : Nat),
          @Eq.{1} ENat (@Houghton.profile.{u_1} G inst E r) (@Nat.cast.{0} ENat ENat.instNatCast n) →
            @LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                r)
              (@Nat.cast.{0} Real Real.instNatCast n))
end

section
/-- Proposition 5.1. Original: `Houghton.dimension_perm`. -/
def proposition_5_1 : Prop :=
  ∀ {Ω : Type} [inst : Fintype.{0} Ω] [inst_1 : DecidableEq.{1} Ω]
  (φ :
    @MonoidHom.{0, 0} Houghton.F (Equiv.Perm.{1} Ω)
      (@MulOneClass.toMulOne.{0} Houghton.F
        (@Monoid.toMulOneClass.{0} Houghton.F
          (@DivInvMonoid.toMonoid.{0} Houghton.F
            (@Group.toDivInvMonoid.{0} Houghton.F
              (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
      (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Ω)
        (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Ω)
          (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Ω)
            (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Ω) (@Equiv.Perm.permGroup.{0} Ω))))))
  (δ : Real)
  (hrel :
    ∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
      @LE.le.{0} Real Real.instLE
        (@Houghton.dH.{0} Ω inst inst_1
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0} Houghton.F (Equiv.Perm.{1} Ω)
              (@MulOneClass.toMulOne.{0} Houghton.F
                (@Monoid.toMulOneClass.{0} Houghton.F
                  (@DivInvMonoid.toMonoid.{0} Houghton.F
                    (@Group.toDivInvMonoid.{0} Houghton.F
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
              (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Ω)
                (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Ω)
                  (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Ω)
                    (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Ω) (@Equiv.Perm.permGroup.{0} Ω))))))
            Houghton.F (fun (x : Houghton.F) => Equiv.Perm.{1} Ω)
            (@MonoidHom.instFunLike.{0, 0} Houghton.F (Equiv.Perm.{1} Ω)
              (@MulOneClass.toMulOne.{0} Houghton.F
                (@Monoid.toMulOneClass.{0} Houghton.F
                  (@DivInvMonoid.toMonoid.{0} Houghton.F
                    (@Group.toDivInvMonoid.{0} Houghton.F
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
              (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Ω)
                (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Ω)
                  (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Ω)
                    (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Ω) (@Equiv.Perm.permGroup.{0} Ω))))))
            φ (Houghton.rel i))
          (@OfNat.ofNat.{0} (Equiv.Perm.{1} Ω) (nat_lit 1)
            (@One.toOfNat1.{0} (Equiv.Perm.{1} Ω) (@Equiv.Perm.instOne.{0} Ω))))
        δ)
  (hγ :
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (@Houghton.dH.{0} Ω inst inst_1
        (@DFunLike.coe.{1, 1, 1}
          (@MonoidHom.{0, 0} Houghton.F (Equiv.Perm.{1} Ω)
            (@MulOneClass.toMulOne.{0} Houghton.F
              (@Monoid.toMulOneClass.{0} Houghton.F
                (@DivInvMonoid.toMonoid.{0} Houghton.F
                  (@Group.toDivInvMonoid.{0} Houghton.F
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
            (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Ω)
              (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Ω)
                (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Ω)
                  (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Ω) (@Equiv.Perm.permGroup.{0} Ω))))))
          Houghton.F (fun (x : Houghton.F) => Equiv.Perm.{1} Ω)
          (@MonoidHom.instFunLike.{0, 0} Houghton.F (Equiv.Perm.{1} Ω)
            (@MulOneClass.toMulOne.{0} Houghton.F
              (@Monoid.toMulOneClass.{0} Houghton.F
                (@DivInvMonoid.toMonoid.{0} Houghton.F
                  (@Group.toDivInvMonoid.{0} Houghton.F
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
            (@MulOneClass.toMulOne.{0} (Equiv.Perm.{1} Ω)
              (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Ω)
                (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Ω)
                  (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Ω) (@Equiv.Perm.permGroup.{0} Ω))))))
          φ Houghton.γ)
        (@OfNat.ofNat.{0} (Equiv.Perm.{1} Ω) (nat_lit 1)
          (@One.toOfNat1.{0} (Equiv.Perm.{1} Ω) (@Equiv.Perm.instOne.{0} Ω)))))
  (N A : Nat) (hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
  (hA :
    Houghton.AstarLE
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N)
      A)
  (hδ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 10)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@Nat.cast.{0} Real Real.instNatCast N))
          (@Nat.cast.{0} Real Real.instNatCast
            (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) A)))
        δ)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast N)
      (@OfNat.ofNat.{0} Real (nat_lit 16)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
    (Real.logb
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{0} Ω inst)))
end

section
/-- Theorem 1.1. Original: `Houghton.theorem_1_1_final`. -/
def theorem_1_1 : Prop :=
  ∀ (r : Real)
  (hr :
    @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      r),
  @Exists.{1} Nat fun (m : Nat) =>
    And
      (@Eq.{1} ENat
        (@Houghton.profile.{0}
          (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
            @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
                (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
              Houghton.H3 x)
          (@Subgroup.toGroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)) Houghton.H3)
          Houghton.E_H r)
        (@Nat.cast.{0} ENat ENat.instNatCast m))
      (And
        (@LE.le.{0} Real Real.instLE
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) r
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (Real.logb
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (@OfNat.ofNat.{0} Real (nat_lit 107)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 107) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 105) (instOfNatNat (nat_lit 105))))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                (@OfNat.ofNat.{0} Real (nat_lit 1280)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 1280) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1279) (instOfNatNat (nat_lit 1279)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1278) (instOfNatNat (nat_lit 1278))))))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 16)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
          (@Nat.cast.{0} Real Real.instNatCast m))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) r
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real (nat_lit 12)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 270)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 270) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 269) (instOfNatNat (nat_lit 269)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268))))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real (nat_lit 16)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
            (@Nat.cast.{0} Real Real.instNatCast m))
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m)
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 7000)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 7000) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6999) (instOfNatNat (nat_lit 6999)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6998) (instOfNatNat (nat_lit 6998)))))))
                  (Real.sqrt r))
                (Real.logb
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  r))))))
end

section
/-- Corollary 1.2. Original: `Houghton.corollary_1_2_final`. -/
def corollary_1_2 : Prop :=
  ∀ (k C : Real),
  @Exists.{1} Real fun (r : Real) =>
    And
      (@LE.le.{0} Real Real.instLE
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        r)
      (@Exists.{1} Nat fun (m : Nat) =>
        And
          (@Eq.{1} ENat
            (@Houghton.profile.{0}
              (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
                @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                    (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                      (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
                    (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                    (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                      (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
                  Houghton.H3 x)
              (@Subgroup.toGroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))
                Houghton.H3)
              Houghton.E_H r)
            (@Nat.cast.{0} ENat ENat.instNatCast m))
          (@LT.lt.{0} Real Real.instLT
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
              (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) r k))
            (@Nat.cast.{0} Real Real.instNatCast m)))
end

section
universe u_1
/-- Corollary 1.3, H3. Original: `Houghton.cremona_finAlt3`. -/
def corollary_1_3 : Prop :=
  ∀ (hS : Houghton.PermSectorBound.{0}) {Γ : Type u_1} [inst : Group.{u_1} Γ]
  (h :
    @MonoidHom.{0, u_1}
      (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
        fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
        @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
            (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
          Houghton.H3 x)
      Γ
      (@MulOneClass.toMulOne.{0}
        (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
          @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
            (@SetLike.instMembership.{0, 0}
              (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
              (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
            Houghton.H3 x)
        (@SubmonoidClass.toMulOneClass.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@MulOpposite.instMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
            (@Monoid.toMulOneClass.{0} (Equiv.Perm.{1} Houghton.Y)
              (@DivInvMonoid.toMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
                (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))))
          (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
          (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
          (@SubgroupClass.toSubmonoidClass.{0, 0}
            (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
            (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y)
              (@Group.toDivInvMonoid.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
            (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
            (@Subgroup.instSubgroupClass.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
          Houghton.H3))
      (@MulOneClass.toMulOne.{u_1} Γ
        (@Monoid.toMulOneClass.{u_1} Γ (@DivInvMonoid.toMonoid.{u_1} Γ (@Group.toDivInvMonoid.{u_1} Γ inst)))))
  (hpoly :
    ∀ (E : Finset.{u_1} Γ),
      @Membership.mem.{u_1, u_1} Γ (Finset.{u_1} Γ)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} Γ) Γ (@Finset.instSetLike.{u_1} Γ)) E
          (@OfNat.ofNat.{u_1} Γ (nat_lit 1)
            (@One.toOfNat1.{u_1} Γ
              (@InvOneClass.toOne.{u_1} Γ
                (@DivInvOneMonoid.toInvOneClass.{u_1} Γ
                  (@DivisionMonoid.toDivInvOneMonoid.{u_1} Γ (@Group.toDivisionMonoid.{u_1} Γ inst)))))) →
        @Exists.{1} Real fun (k : Real) =>
          @Exists.{1} Real fun (C : Real) =>
            @Exists.{1} Real fun (R : Real) =>
              ∀ (r : Real),
                @LE.le.{0} Real Real.instLE R r →
                  @Exists.{1} Nat fun (m : Nat) =>
                    And (@Eq.{1} ENat (@Houghton.profile.{u_1} Γ inst E r) (@Nat.cast.{0} ENat ENat.instNatCast m))
                      (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) r k)))),
  @LE.le.{0}
    (@Subgroup.{0}
      (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
        fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
        @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
            (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
          Houghton.H3 x)
      (@Subgroup.toGroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
        (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)) Houghton.H3))
    (@Preorder.toLE.{0}
      (@Subgroup.{0}
        (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
          @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
            (@SetLike.instMembership.{0, 0}
              (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
              (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
            Houghton.H3 x)
        (@Subgroup.toGroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)) Houghton.H3))
      (@PartialOrder.toPreorder.{0}
        (@Subgroup.{0}
          (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
            @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
                (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
              Houghton.H3 x)
          (@Subgroup.toGroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))
            Houghton.H3))
        (@Subgroup.instPartialOrder.{0}
          (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
            @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
                (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
                  (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
              Houghton.H3 x)
          (@Subgroup.toGroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))
            Houghton.H3))))
    Houghton.finAlt3
    (@MonoidHom.ker.{0, u_1}
      (@Subtype.{1} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
        fun (x : MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y)) =>
        @Membership.mem.{0, 0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
          (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)))
            (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
            (@Subgroup.instSetLike.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
              (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y))))
          Houghton.H3 x)
      (@Subgroup.toGroup.{0} (MulOpposite.{0} (Equiv.Perm.{1} Houghton.Y))
        (@MulOpposite.instGroup.{0} (Equiv.Perm.{1} Houghton.Y) (@Equiv.Perm.permGroup.{0} Houghton.Y)) Houghton.H3)
      Γ (@Monoid.toMulOneClass.{u_1} Γ (@DivInvMonoid.toMonoid.{u_1} Γ (@Group.toDivInvMonoid.{u_1} Γ inst))) h)
end

end PaperStatements
