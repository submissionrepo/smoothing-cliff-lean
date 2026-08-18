/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Kuhn.Converse
public import Econlib.GameTheory.ExtensiveForm.Kuhn.PerfectRecall
public import Econlib.GameTheory.ExtensiveForm.Refinements.PBE

/-!
# Reach-probability invariance across an information set under unilateral deviation

The supporting lemma for the extensive-form one-shot deviation principle. Under perfect recall, a
unilateral `i`-deviation rescales the reach probability of every node in a fixed information set
`(i, ω)` by the same factor. Stated in cross-multiplied form
`reachProb σ' x * reachProb σ x' =
reachProb σ' x' * reachProb σ x` for `x, x'` two reachable
histories in the same information set, this needs no division and no positivity hypothesis.

## Main definitions

* `FiniteExtensiveForm.iMarginal`: The per-player realization marginal of `reachProb`.

## Main statements

* `FiniteExtensiveForm.realization_factor`: The chance × per-player-marginal factorization of
  `reachProb`.
* `FiniteExtensiveForm.iMarginal_invariant_of_ne`: A co-player's marginal is deviation-invariant.
* `FiniteExtensiveForm.iMarginal_repr_invariant`: The moving player's marginal is
  representative-independent across an information set.
* `reachProb_infoSet_invariant_unilateral`: Reach-probability invariance across an information set.

## Notes

The proof factors the behavioral reach probability through the chance weight and a per-player
marginal of pure path-consistency (`realization_factor`), then closes the cross-multiplication from
`iMarginal_invariant_of_ne` for the co-players and `iMarginal_repr_invariant` (action recall) for
the deviating player.

## Tags

extensive form, reach probability, perfect recall, one-shot deviation principle, realization
-/

@[expose] public noncomputable section

open BigOperators Econlib.Probability

namespace Econlib.GameTheory

universe u

/-! ## Abstract marginalization: Agreement on a coordinate sub-block

If two product densities `∏ f` and `∏ g` over a Pi type agree on the coordinates of a predicate
`p`, the off-`p` factors of each sum to one, and the integrand `P` depends only on the
`p`-coordinates, then their `P`-weighted sums coincide: The off-`p` block marginalizes away to one
on both sides. -/

namespace AbstractMarginal

/-- Marginalization of a coordinate sub-block. The non-`p` coordinates of `f` and `g` each sum to
one and `P` ignores them, so they wash out; on the `p`-coordinates `f` and `g` agree. -/
lemma sum_prod_eq_of_agree_on_pred
    {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
    [∀ i, Inhabited (β i)] (p : ι → Prop)
    (f g : ∀ i, β i → ℝ)
    (hfg : ∀ i, p i → f i = g i)
    (hf1 : ∀ i, ¬ p i → ∑ a : β i, f i a = 1)
    (hg1 : ∀ i, ¬ p i → ∑ a : β i, g i a = 1)
    (P : (∀ i, β i) → ℝ)
    (hP : ∀ c c' : ∀ i, β i, (∀ i, p i → c i = c' i) → P c = P c') :
    ∑ c : ∀ i, β i, (∏ i, f i (c i)) * P c = ∑ c : ∀ i, β i, (∏ i, g i (c i)) * P c := by
  classical
  set e : (∀ i, β i) ≃ ((i : {x // p x}) → β ↑i) × ((i : {x // ¬ p x}) → β ↑i) :=
    Equiv.piEquivPiSubtypeProd p β with he
  -- A reusable reduction: any product density `h` with off-`p` block summing to 1 collapses to a
  -- sum over the `p`-block only, weighting `P` evaluated on the reconstructed profile.
  have reduce : ∀ (h : ∀ i, β i → ℝ), (∀ i, ¬ p i → ∑ a : β i, h i a = 1) →
      ∑ c : ∀ i, β i, (∏ i, h i (c i)) * P c =
        ∑ cp : (i : {x // p x}) → β ↑i,
          (∏ i : {x // p x}, h ↑i (cp i)) * P (e.symm (cp, fun _ => default)) := by
    intro h hh1
    rw [← Equiv.sum_comp e.symm]
    -- rewrite the integrand on each `(cp, cnp)` pair
    have key : ∀ q : ((i : {x // p x}) → β ↑i) × ((i : {x // ¬ p x}) → β ↑i),
        (∏ i, h i (e.symm q i)) * P (e.symm q) =
          (∏ i : {x // p x}, h ↑i (q.1 i)) * P (e.symm (q.1, fun _ => default)) *
            ∏ i : {x // ¬ p x}, h ↑i (q.2 i) := by
      intro q
      -- split the full product into the `p`- and `¬p`-blocks
      have hsplit : (∏ i, h i (e.symm q i)) =
          (∏ i : {x // p x}, h ↑i (q.1 i)) * ∏ i : {x // ¬ p x}, h ↑i (q.2 i) := by
        rw [← Fintype.prod_subtype_mul_prod_subtype p (fun i => h i (e.symm q i))]
        congr 1
        · exact Finset.prod_congr rfl fun i _ => by
            simp only [he, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2]
        · exact Finset.prod_congr rfl fun i _ => by
            simp only [he, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
      -- `P` ignores the off-`p` block
      have hPq : P (e.symm q) = P (e.symm (q.1, fun _ => default)) := by
        apply hP
        intro i hpi
        simp only [he, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hpi]
      rw [hsplit, hPq]; ring
    rw [Finset.sum_congr rfl (fun q _ => key q)]
    -- Fubini over the product index, then collapse the `¬p`-block to one.
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun cp _ => ?_
    simp only
    -- the `¬p`-block sum collapses to one
    have hcnp : ∑ cnp : (i : {x // ¬ p x}) → β ↑i, ∏ i : {x // ¬ p x}, h ↑i (cnp i) = 1 := by
      rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
      exact Finset.prod_eq_one fun i _ => hh1 ↑i i.2
    rw [← Finset.mul_sum, hcnp, mul_one]
  -- Apply `reduce` to both `f` and `g`; the `p`-block products and `P`-terms then match.
  rw [reduce f hf1, reduce g hg1]
  refine Finset.sum_congr rfl fun cp _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [hfg ↑i i.2]

end AbstractMarginal

variable {I E : Type u} [DecidableEq E] [DecidableEq I]

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E)

/-- The per-player realization marginal: The expected path-consistency weight that player `j`'s
behaviorally-induced mixed strategy assigns to reaching `h`. -/
noncomputable def iMarginal (σ : G.toExtensiveForm.BehavioralStrategy) (j : I) (h : List E) : ℝ :=
  ∑ c : G.PureStrategy j, (G.behavioralToMixed σ j).val c * G.iPathConsistent j c h

/-- **Realization factorization of `reachProb`.** The behavioral reach probability factors as the
chance-only weight times the product over players of their realization marginals. -/
theorem realization_factor [Fintype I] (G : PerfectRecallFiniteExtensiveForm I E)
    (σ : G.toExtensiveForm.BehavioralStrategy) (h : List E)
    (h_reach : h ∈ G.toFiniteExtensiveForm.reach) :
    reachProb G.toExtensiveForm σ h =
      G.toFiniteExtensiveForm.chanceWeight h *
        ∏ j, G.toFiniteExtensiveForm.iMarginal σ j h := by
  unfold reachProb ExtensiveForm.finitePrefixProb iMarginal
  have hreal := G.toFiniteExtensiveForm.realization_aux G.perfectRecall.noInfoSetRevisit σ [] h
    G.toFiniteExtensiveForm.nil_mem_reach (by rw [List.nil_append]; exact h_reach)
  rw [hreal]
  have hfub := G.toFiniteExtensiveForm.sum_prod_pureReachProb_eq
    (fun j => G.toFiniteExtensiveForm.behavioralToMixed σ j) h
  unfold FiniteExtensiveForm.pureReachProb at hfub
  rw [hfub]

omit [DecidableEq E] [DecidableEq I] in
/-- At a reached info set `(j, obs)` with `j ≠ i`, the node-local behavior at the canonical
representative is invariant under a unilateral `i`-deviation: The representative is a `j`-mover
node, so the behavior reads only player `j`'s coordinate, on which `σ` and `σ'` agree. -/
lemma atHistory_canonicalRep_eq_of_ne (G : FiniteExtensiveForm I E)
    (i j : I) (hij : j ≠ i)
    (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i σ σ')
    (obs : G.info.Obs j) (h_reached : G.IsReachedInfoSet j obs) :
    σ'.atHistory (G.canonicalRep j obs) = σ.atHistory (G.canonicalRep j obs) := by
  -- At the canonical rep, `j` moves; identify the player node there.
  obtain ⟨_, _, h_canon_move⟩ := G.canonicalRep_spec j obs h_reached
  obtain ⟨n, hk, hmover⟩ : ∃ n : PlayerNode I E,
      G.tree.nodeKind (G.canonicalRep j obs) = .player n ∧ n.mover = j := by
    rcases hk : G.tree.nodeKind (G.canonicalRep j obs) with _ | n | n | n | n
    · rw [hk] at h_canon_move; exact absurd h_canon_move id
    · exact ⟨n, rfl, by rw [hk] at h_canon_move; exact h_canon_move⟩
    · exact absurd hk (G.no_joint _ n)
    · rw [hk] at h_canon_move; exact absurd h_canon_move id
    · exact absurd hk (G.no_general_chance _ n)
  -- Only player `j`'s coordinate is read, and `σ' j = σ j` since `j ≠ i`.
  apply eq_of_heq
  refine (σ'.atHistory_player_heq hk).trans (HEq.trans ?_ (σ.atHistory_player_heq hk).symm)
  rw [hmover]
  exact heq_of_eq (hdev j _ hij)

/-- **Co-player factor invariance.** For a player `j ≠ i`, a unilateral `i`-deviation leaves the
realization marginal of `j` unchanged on a reachable history. -/
theorem iMarginal_invariant_of_ne (G : PerfectRecallFiniteExtensiveForm I E)
    (i j : I) (hij : j ≠ i)
    (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i σ σ')
    (h : List E) (h_reach : h ∈ G.toFiniteExtensiveForm.reach) :
    G.toFiniteExtensiveForm.iMarginal σ' j h = G.toFiniteExtensiveForm.iMarginal σ j h := by
  classical
  unfold FiniteExtensiveForm.iMarginal FiniteExtensiveForm.behavioralToMixed
    FiniteExtensiveForm.behavioralToMixedFactor
  simp only
  -- Apply the abstract marginalization with `p obs := info set (j,obs) is reached`.
  refine AbstractMarginal.sum_prod_eq_of_agree_on_pred
    (β := fun obs => G.toFiniteExtensiveForm.infoSetChoiceForObs j obs)
    (p := fun obs => G.toFiniteExtensiveForm.IsReachedInfoSet j obs)
    (f := fun obs a => (G.toExtensiveForm.tree.nodeKind
      (G.toFiniteExtensiveForm.canonicalRep j obs)).behaviorEval
      (σ'.atHistory (G.toFiniteExtensiveForm.canonicalRep j obs)) a)
    (g := fun obs a => (G.toExtensiveForm.tree.nodeKind
      (G.toFiniteExtensiveForm.canonicalRep j obs)).behaviorEval
      (σ.atHistory (G.toFiniteExtensiveForm.canonicalRep j obs)) a)
    ?_ ?_ ?_ (P := fun c => G.toFiniteExtensiveForm.iPathConsistent j c h) ?_
  · -- agreement on reached info sets
    intro obs hreached
    funext a
    simp only
    rw [G.toFiniteExtensiveForm.atHistory_canonicalRep_eq_of_ne i j hij σ σ' hdev obs hreached]
  · -- non-reached `σ'` factors sum to one
    intro obs _; exact NodeKind.behaviorEval_sum_one _ _
  · -- non-reached `σ` factors sum to one
    intro obs _; exact NodeKind.behaviorEval_sum_one _ _
  · -- `iPathConsistent` only depends on reached coordinates of `c`
    intro c c' hcc'
    apply G.toFiniteExtensiveForm.iPathConsistentFrom_eq_of_eq_on_path
    intro k _ hmove
    -- the prefix `[] ++ h.take k = h.take k` is reachable and `j` moves there ⟹ info set reached
    have hpre_reach : (h.take k) ∈ G.toFiniteExtensiveForm.reach :=
      G.toFiniteExtensiveForm.reach_take_of_reach h h_reach k
    rw [List.nil_append] at hmove ⊢
    exact hcc' (G.toExtensiveForm.info.observe j (h.take k))
      ⟨h.take k, hpre_reach, rfl, hmove⟩

/-- **Representative independence of the moving player's factor.** For the deviating player `i`,
the realization marginal is the same at any two reachable histories in the same information set —
this is exactly action recall, applied term by term. -/
theorem iMarginal_repr_invariant (G : PerfectRecallFiniteExtensiveForm I E)
    (har : G.toFiniteExtensiveForm.ActionRecall)
    (i : I) (σ : G.toExtensiveForm.BehavioralStrategy)
    (x x' : List E)
    (hx_reach : x ∈ G.toFiniteExtensiveForm.reach) (hx'_reach : x' ∈ G.toFiniteExtensiveForm.reach)
    (hmx : (G.toExtensiveForm.tree.nodeKind x).movesAt i)
    (hmx' : (G.toExtensiveForm.tree.nodeKind x').movesAt i)
    (hobs : G.toExtensiveForm.info.observe i x = G.toExtensiveForm.info.observe i x') :
    G.toFiniteExtensiveForm.iMarginal σ i x = G.toFiniteExtensiveForm.iMarginal σ i x' := by
  unfold FiniteExtensiveForm.iMarginal
  -- Each path-consistency term is representative-independent by action recall.
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  -- Bridge the ambient `DecidableEq` instances to the `Classical` ones used by `actionRecall`.
  rw [← G.toFiniteExtensiveForm.iPathConsistent_classical_eq i c x,
    ← G.toFiniteExtensiveForm.iPathConsistent_classical_eq i c x']
  exact har i c x x' hx_reach hx'_reach hmx hmx' hobs

end FiniteExtensiveForm

variable [Finite I]

omit [DecidableEq I] in
/-- **Reach-probability invariance across an information set under unilateral deviation** (bundled
perfect-recall form). Under perfect recall, a unilateral `i`-deviation `σ → σ'` rescales the reach
probability of every node in the information set `(i, ω)` by the same factor. The cross-multiplied
form needs no positivity hypothesis. -/
theorem reachProb_infoSet_invariant_unilateral'
    (G : PerfectRecallFiniteExtensiveForm I E)
    (i : I) (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i σ σ')
    (ω : G.toExtensiveForm.info.Obs i) (x x' : List E)
    (hx_reach : x ∈ G.toFiniteExtensiveForm.reach)
    (hx'_reach : x' ∈ G.toFiniteExtensiveForm.reach)
    (hx : (G.toExtensiveForm.tree.nodeKind x).movesAt i ∧ G.toExtensiveForm.info.observe i x = ω)
    (hx' : (G.toExtensiveForm.tree.nodeKind x').movesAt i ∧
      G.toExtensiveForm.info.observe i x' = ω) :
    reachProb G.toExtensiveForm σ' x * reachProb G.toExtensiveForm σ x' =
      reachProb G.toExtensiveForm σ' x' * reachProb G.toExtensiveForm σ x := by
  classical
  obtain ⟨hmx, hox⟩ := hx
  obtain ⟨hmx', hox'⟩ := hx'
  have hobs : G.toExtensiveForm.info.observe i x = G.toExtensiveForm.info.observe i x' := by
    rw [hox, hox']
  have hif : Fintype I := Fintype.ofFinite I
  -- Factor every reach probability through the chance weight and the per-player marginals.
  rw [FiniteExtensiveForm.realization_factor G σ' x hx_reach,
    FiniteExtensiveForm.realization_factor G σ x' hx'_reach,
    FiniteExtensiveForm.realization_factor G σ' x' hx'_reach,
    FiniteExtensiveForm.realization_factor G σ x hx_reach]
  -- It suffices to equate the per-player products (chance weights cancel by commutativity).
  have hmain : (∏ j, G.toFiniteExtensiveForm.iMarginal σ' j x) *
        ∏ j, G.toFiniteExtensiveForm.iMarginal σ j x' =
      (∏ j, G.toFiniteExtensiveForm.iMarginal σ' j x') *
        ∏ j, G.toFiniteExtensiveForm.iMarginal σ j x := by
    -- split each product into the `i`-factor and the co-player product over `univ.erase i`
    have hsplit : ∀ (τ : G.toExtensiveForm.BehavioralStrategy) (h : List E),
        (∏ j, G.toFiniteExtensiveForm.iMarginal τ j h) =
          G.toFiniteExtensiveForm.iMarginal τ i h *
            ∏ j ∈ Finset.univ.erase i, G.toFiniteExtensiveForm.iMarginal τ j h := fun τ h =>
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
    -- the co-player products are deviation-invariant
    have hco : ∀ (h : List E), h ∈ G.toFiniteExtensiveForm.reach →
        (∏ j ∈ Finset.univ.erase i, G.toFiniteExtensiveForm.iMarginal σ' j h) =
          ∏ j ∈ Finset.univ.erase i, G.toFiniteExtensiveForm.iMarginal σ j h := fun h hr =>
      Finset.prod_congr rfl fun j hj =>
        FiniteExtensiveForm.iMarginal_invariant_of_ne G i j (Finset.ne_of_mem_erase hj)
          σ σ' hdev h hr
    -- the `i`-factor is representative-independent (action recall)
    have hreprσ' := FiniteExtensiveForm.iMarginal_repr_invariant G G.perfectRecall.actionRecall
      i σ' x x' hx_reach hx'_reach hmx hmx' hobs
    have hreprσ := FiniteExtensiveForm.iMarginal_repr_invariant G G.perfectRecall.actionRecall
      i σ x x' hx_reach hx'_reach hmx hmx' hobs
    rw [hsplit σ' x, hsplit σ x', hsplit σ' x', hsplit σ x,
      hco x hx_reach, hco x' hx'_reach, hreprσ', hreprσ]
    ring
  rw [mul_mul_mul_comm, mul_mul_mul_comm
    (G.toFiniteExtensiveForm.chanceWeight x') _, hmain]
  ring

omit [DecidableEq I] in
/-- **Reach-probability invariance across an information set under unilateral deviation** — the
linchpin lemma for the extensive-form one-shot deviation principle. Under perfect recall, a
unilateral `i`-deviation `σ → σ'` rescales the reach probability of every node in the information
set `(i, ω)` by the same factor. The cross-multiplied form needs no positivity hypothesis. The two
histories `x, x'` must be reachable (the OSDP consumer supplies reachability). -/
theorem reachProb_infoSet_invariant_unilateral
    (G : FiniteExtensiveForm I E) (hpr : G.IsPerfectRecall)
    (i : I) (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i σ σ')
    (ω : G.toExtensiveForm.info.Obs i) (x x' : List E)
    (hx_reach : x ∈ G.reach) (hx'_reach : x' ∈ G.reach)
    (hx : (G.toExtensiveForm.tree.nodeKind x).movesAt i ∧ G.toExtensiveForm.info.observe i x = ω)
    (hx' : (G.toExtensiveForm.tree.nodeKind x').movesAt i ∧
      G.toExtensiveForm.info.observe i x' = ω) :
    reachProb G.toExtensiveForm σ' x * reachProb G.toExtensiveForm σ x' =
      reachProb G.toExtensiveForm σ' x' * reachProb G.toExtensiveForm σ x := by
  have hif : Fintype I := Fintype.ofFinite I
  exact reachProb_infoSet_invariant_unilateral' ⟨G, hpr⟩ i σ σ' hdev ω x x'
    hx_reach hx'_reach hx hx'

end Econlib.GameTheory
