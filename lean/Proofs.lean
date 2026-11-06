import Statements
set_option maxRecDepth 100000

namespace PaperProofs

section
/-- Theorem 3.1. -/
theorem theorem_3_1 : PaperStatements.theorem_3_1 :=
  @Houghton.astar_le_pow
end

section
/-- Theorem 3.2. -/
theorem theorem_3_2 : PaperStatements.theorem_3_2 :=
  @Houghton.astar_le_weighted_rpow
end

section
/-- Theorem 3.3. -/
theorem theorem_3_3 : PaperStatements.theorem_3_3 :=
  @Houghton.dehn_bound
end

section
/-- Theorem 3.3, polynomial consequence. -/
theorem theorem_3_3_polynomial : PaperStatements.theorem_3_3_polynomial :=
  @Houghton.dehn_poly_weighted
end

section
/-- Johnson presentation. -/
theorem johnson_presentation : PaperStatements.johnson_presentation :=
  @Houghton.null_iff_areaLE
end

section
universe u_1
/-- Lemma 2.1, embedding. -/
theorem lemma_2_1_embedding : PaperStatements.lemma_2_1_embedding.{u_1} :=
  @Houghton.embeds_of_profile_lt.{u_1}
end

section
universe u_1
/-- Lemma 2.1, dichotomy. -/
theorem lemma_2_1_dichotomy : PaperStatements.lemma_2_1_dichotomy.{u_1} :=
  @Houghton.profile_bounded_or_ge.{u_1}
end

section
/-- Proposition 5.1. -/
theorem proposition_5_1 : PaperStatements.proposition_5_1 :=
  @Houghton.dimension_perm
end

section
/-- Theorem 1.1. -/
theorem theorem_1_1 : PaperStatements.theorem_1_1 :=
  @Houghton.theorem_1_1_final
end

section
/-- Corollary 1.2. -/
theorem corollary_1_2 : PaperStatements.corollary_1_2 :=
  @Houghton.corollary_1_2_final
end

section
universe u_1
/-- Corollary 1.3, H3. -/
theorem corollary_1_3 : PaperStatements.corollary_1_3.{u_1} :=
  @Houghton.cremona_finAlt3.{u_1}
end

end PaperProofs
