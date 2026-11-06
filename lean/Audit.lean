import Proofs
set_option maxRecDepth 100000

/-! Frozen exact-type checks and axiom audit of every headline. -/

-- Theorem 3.1
#check (@Houghton.astar_le_pow : PaperStatements.theorem_3_1)
#print axioms Houghton.astar_le_pow
#print axioms PaperProofs.theorem_3_1

-- Theorem 3.2
#check (@Houghton.astar_le_weighted_rpow : PaperStatements.theorem_3_2)
#print axioms Houghton.astar_le_weighted_rpow
#print axioms PaperProofs.theorem_3_2

-- Theorem 3.3
#check (@Houghton.dehn_bound : PaperStatements.theorem_3_3)
#print axioms Houghton.dehn_bound
#print axioms PaperProofs.theorem_3_3

-- Theorem 3.3, polynomial consequence
#check (@Houghton.dehn_poly_weighted : PaperStatements.theorem_3_3_polynomial)
#print axioms Houghton.dehn_poly_weighted
#print axioms PaperProofs.theorem_3_3_polynomial

-- Johnson presentation
#check (@Houghton.null_iff_areaLE : PaperStatements.johnson_presentation)
#print axioms Houghton.null_iff_areaLE
#print axioms PaperProofs.johnson_presentation

-- Lemma 2.1, embedding
#check (@Houghton.embeds_of_profile_lt : PaperStatements.lemma_2_1_embedding)
#print axioms Houghton.embeds_of_profile_lt
#print axioms PaperProofs.lemma_2_1_embedding

-- Lemma 2.1, dichotomy
#check (@Houghton.profile_bounded_or_ge : PaperStatements.lemma_2_1_dichotomy)
#print axioms Houghton.profile_bounded_or_ge
#print axioms PaperProofs.lemma_2_1_dichotomy

-- Proposition 5.1
#check (@Houghton.dimension_perm : PaperStatements.proposition_5_1)
#print axioms Houghton.dimension_perm
#print axioms PaperProofs.proposition_5_1

-- Theorem 1.1
#check (@Houghton.theorem_1_1_final : PaperStatements.theorem_1_1)
#print axioms Houghton.theorem_1_1_final
#print axioms PaperProofs.theorem_1_1

-- Corollary 1.2
#check (@Houghton.corollary_1_2_final : PaperStatements.corollary_1_2)
#print axioms Houghton.corollary_1_2_final
#print axioms PaperProofs.corollary_1_2

-- Corollary 1.3, H3
#check (@Houghton.cremona_finAlt3 : PaperStatements.corollary_1_3)
#print axioms Houghton.cremona_finAlt3
#print axioms PaperProofs.corollary_1_3

-- Additional original audit root: Houghton.dimension_perm_of_SSA
section
universe u
example : ∀ (hQ : Houghton.QIT_CommutingPinchingSSA.{u}) {Ω : Type u} [inst : Fintype.{u} Ω] [inst_1 : DecidableEq.{u + 1} Ω]
  (φ :
    @MonoidHom.{0, u} Houghton.F (Equiv.Perm.{u + 1} Ω)
      (@MulOneClass.toMulOne.{0} Houghton.F
        (@Monoid.toMulOneClass.{0} Houghton.F
          (@DivInvMonoid.toMonoid.{0} Houghton.F
            (@Group.toDivInvMonoid.{0} Houghton.F
              (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
      (@MulOneClass.toMulOne.{u} (Equiv.Perm.{u + 1} Ω)
        (@Monoid.toMulOneClass.{u} (Equiv.Perm.{u + 1} Ω)
          (@DivInvMonoid.toMonoid.{u} (Equiv.Perm.{u + 1} Ω)
            (@Group.toDivInvMonoid.{u} (Equiv.Perm.{u + 1} Ω) (@Equiv.Perm.permGroup.{u} Ω))))))
  (δ : Real)
  (hrel :
    ∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
      @LE.le.{0} Real Real.instLE
        (@Houghton.dH.{u} Ω inst inst_1
          (@DFunLike.coe.{u + 1, 1, u + 1}
            (@MonoidHom.{0, u} Houghton.F (Equiv.Perm.{u + 1} Ω)
              (@MulOneClass.toMulOne.{0} Houghton.F
                (@Monoid.toMulOneClass.{0} Houghton.F
                  (@DivInvMonoid.toMonoid.{0} Houghton.F
                    (@Group.toDivInvMonoid.{0} Houghton.F
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
              (@MulOneClass.toMulOne.{u} (Equiv.Perm.{u + 1} Ω)
                (@Monoid.toMulOneClass.{u} (Equiv.Perm.{u + 1} Ω)
                  (@DivInvMonoid.toMonoid.{u} (Equiv.Perm.{u + 1} Ω)
                    (@Group.toDivInvMonoid.{u} (Equiv.Perm.{u + 1} Ω) (@Equiv.Perm.permGroup.{u} Ω))))))
            Houghton.F (fun (x : Houghton.F) => Equiv.Perm.{u + 1} Ω)
            (@MonoidHom.instFunLike.{0, u} Houghton.F (Equiv.Perm.{u + 1} Ω)
              (@MulOneClass.toMulOne.{0} Houghton.F
                (@Monoid.toMulOneClass.{0} Houghton.F
                  (@DivInvMonoid.toMonoid.{0} Houghton.F
                    (@Group.toDivInvMonoid.{0} Houghton.F
                      (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
              (@MulOneClass.toMulOne.{u} (Equiv.Perm.{u + 1} Ω)
                (@Monoid.toMulOneClass.{u} (Equiv.Perm.{u + 1} Ω)
                  (@DivInvMonoid.toMonoid.{u} (Equiv.Perm.{u + 1} Ω)
                    (@Group.toDivInvMonoid.{u} (Equiv.Perm.{u + 1} Ω) (@Equiv.Perm.permGroup.{u} Ω))))))
            φ (Houghton.rel i))
          (@OfNat.ofNat.{u} (Equiv.Perm.{u + 1} Ω) (nat_lit 1)
            (@One.toOfNat1.{u} (Equiv.Perm.{u + 1} Ω) (@Equiv.Perm.instOne.{u} Ω))))
        δ)
  (hγ :
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (@Houghton.dH.{u} Ω inst inst_1
        (@DFunLike.coe.{u + 1, 1, u + 1}
          (@MonoidHom.{0, u} Houghton.F (Equiv.Perm.{u + 1} Ω)
            (@MulOneClass.toMulOne.{0} Houghton.F
              (@Monoid.toMulOneClass.{0} Houghton.F
                (@DivInvMonoid.toMonoid.{0} Houghton.F
                  (@Group.toDivInvMonoid.{0} Houghton.F
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
            (@MulOneClass.toMulOne.{u} (Equiv.Perm.{u + 1} Ω)
              (@Monoid.toMulOneClass.{u} (Equiv.Perm.{u + 1} Ω)
                (@DivInvMonoid.toMonoid.{u} (Equiv.Perm.{u + 1} Ω)
                  (@Group.toDivInvMonoid.{u} (Equiv.Perm.{u + 1} Ω) (@Equiv.Perm.permGroup.{u} Ω))))))
          Houghton.F (fun (x : Houghton.F) => Equiv.Perm.{u + 1} Ω)
          (@MonoidHom.instFunLike.{0, u} Houghton.F (Equiv.Perm.{u + 1} Ω)
            (@MulOneClass.toMulOne.{0} Houghton.F
              (@Monoid.toMulOneClass.{0} Houghton.F
                (@DivInvMonoid.toMonoid.{0} Houghton.F
                  (@Group.toDivInvMonoid.{0} Houghton.F
                    (@FreeGroup.instGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
            (@MulOneClass.toMulOne.{u} (Equiv.Perm.{u + 1} Ω)
              (@Monoid.toMulOneClass.{u} (Equiv.Perm.{u + 1} Ω)
                (@DivInvMonoid.toMonoid.{u} (Equiv.Perm.{u + 1} Ω)
                  (@Group.toDivInvMonoid.{u} (Equiv.Perm.{u + 1} Ω) (@Equiv.Perm.permGroup.{u} Ω))))))
          φ Houghton.γ)
        (@OfNat.ofNat.{u} (Equiv.Perm.{u + 1} Ω) (nat_lit 1)
          (@One.toOfNat1.{u} (Equiv.Perm.{u + 1} Ω) (@Equiv.Perm.instOne.{u} Ω)))))
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
      (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u} Ω inst))) := @Houghton.dimension_perm_of_SSA.{u}
end
#print axioms Houghton.dimension_perm_of_SSA

-- Additional original audit root: Houghton.theorem_1_1_SSA
section
example : ∀ (hQ : Houghton.QIT_CommutingPinchingSSA.{0}) (r : Real)
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
                  r)))))) := @Houghton.theorem_1_1_SSA
end
#print axioms Houghton.theorem_1_1_SSA

-- Additional original audit root: Houghton.theorem_1_1_upper
section
example : ∀ (r : Real)
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
              r)))) := @Houghton.theorem_1_1_upper
end
#print axioms Houghton.theorem_1_1_upper

-- Additional original audit root: Houghton.corollary_1_2_SSA
section
example : ∀ (hQ : Houghton.QIT_CommutingPinchingSSA.{0}) (k C : Real),
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
            (@Nat.cast.{0} Real Real.instNatCast m))) := @Houghton.corollary_1_2_SSA
end
#print axioms Houghton.corollary_1_2_SSA

-- Additional original audit root: Houghton.permSectorBound_of_SSA
section
example : ∀ (hQ : Houghton.QIT_CommutingPinchingSSA.{0}), Houghton.PermSectorBound.{0} := @Houghton.permSectorBound_of_SSA
end
#print axioms Houghton.permSectorBound_of_SSA
