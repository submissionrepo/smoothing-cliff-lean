/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.SolutionConcepts

/-!
# The taxation principle

The **taxation principle** (Rochet 1985): Under dominant-strategy incentive compatibility, an
agent's transfer depends on its own report only through the allocation that report induces (holding
the others' reports fixed), so two own-reports yielding the same outcome are charged the same
amount. Equivalently, a DSIC mechanism is implemented by posting, for each agent, a price **menu
over outcomes**; the agent picks its favorite `(outcome, price)` pair, and that choice reproduces
the mechanism's allocation and transfer at the agent's true type. This file develops the
finite-type form: The invariance lemma, the posted menu, an optimality (existence-of-optimal-entry)
version, and a unique-implementation version under a strict-incentive condition.

## Main definitions

* `menu`: The posted price menu for an agent — the set of `(outcome, transfer)` pairs reachable by
  varying its own report.
* `menuUtility`: The agent's quasilinear utility from a menu entry at its true type.
* `truthfulEntry`: The menu entry produced by truthful reporting.
* `StrictlySeparatesAlloc`: The strict-incentive condition — every own-report inducing a different
  outcome is strictly worse — under which the menu choice is unique.

## Main statements

* `DirectMechanism.IsDSIC.transfer_eq_of_alloc_eq`: Same induced outcome ⇒ same transfer.
* `menu_transfer_well_defined`: The menu is a price over outcomes (one price per outcome).
* `implements_menu`: Under DSIC, the truthful entry maximizes the agent's menu utility, so it is an
  optimal entry of the posted menu.
* `menu_choice_eq_mechanism`: Packaged implementation — the truthful entry lies in the menu, is an
  optimal entry, and its outcome and price are the DSIC allocation and transfer at the true type.
* `menu_maximizer_unique`: Under DSIC and `StrictlySeparatesAlloc`, the truthful entry is the
  unique menu-utility maximizer, so the optimizing agent chooses exactly the DSIC outcome and price.

## Notes

Unlike the Green–Laffont uniqueness result (efficient + DSIC ⇒ Groves), which requires a connected
type domain and is therefore vacuous on finite type spaces, the taxation principle holds verbatim
for finite types. `implements_menu` is optimality only; a misreport inducing a different outcome
can tie the truthful menu utility, which is why uniqueness of the agent's choice requires the
additional hypothesis `StrictlySeparatesAlloc`.

## References

* Rochet, J.C. 1985. “The Taxation Principle and Multi-Time Hamilton-Jacobi Equations.” *Journal of
  Mathematical Economics* 14 (2): 113–28. [https://doi.org/10.1016/0304-4068(85)90015-1](https://doi.org/10.1016/0304-4068(85)90015-1).

## Tags

taxation principle, dsic, menu, holmström
-/

@[expose] public section

open Function

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

variable {E : QuasilinearEnvironment} {M : DirectMechanism E}

/-- **Taxation principle** (Rochet 1985). If two reports of agent `i` (with the others' reports `r`
held fixed) induce the same allocation, a DSIC mechanism charges them the same transfer. -/
theorem DirectMechanism.IsDSIC.transfer_eq_of_alloc_eq (hM : M.IsDSIC)
    (i : E.Agent) (r : E.TypeProfile) (a b : E.Theta i)
    (hall : M.alloc (update r i a) = M.alloc (update r i b)) :
    M.transfer i (update r i a) = M.transfer i (update r i b) := by
  have hab := hM i r a b
  have hba := hM i r b a
  simp only [DirectMechanism.exPostUtility_def, hall] at hab hba
  exact le_antisymm (by linarith [hba]) (by linarith [hab])

/-! ### The posted price menu

The taxation principle is usually stated as an implementation: A DSIC mechanism is equivalent
to posting, for each agent, a price menu over outcomes; the agent picks its favorite
`(outcome, price)` pair, and that choice reproduces the mechanism's allocation and transfer at its
true type. The menu is the set of `(outcome, transfer)` pairs the agent can reach by varying its
own report (others' reports fixed). The invariance lemma `transfer_eq_of_alloc_eq` is what makes
this a price over outcomes: Distinct reports inducing the same outcome carry the same price. -/

variable (M) in
/-- The **posted price menu** for agent `i`, given the others' reports recorded in the base profile
`r`: The set of `(outcome, transfer)` pairs the agent can reach by varying its own report. Each
reachable report `s` contributes the pair
`(M.alloc (update r i s), M.transfer i (update r i s))`. -/
def menu (i : E.Agent) (r : E.TypeProfile) : Set (E.Outcome × ℝ) :=
  Set.range fun s : E.Theta i => (M.alloc (update r i s), M.transfer i (update r i s))

/-- The menu is a **price over outcomes**: Two menu entries with the same outcome carry the same
price. This is the taxation principle (`transfer_eq_of_alloc_eq`) packaged as well-definedness of
the menu price as a function of the outcome. -/
lemma menu_transfer_well_defined (hM : M.IsDSIC) (i : E.Agent) (r : E.TypeProfile)
    {o : E.Outcome} {t₁ t₂ : ℝ} (h₁ : (o, t₁) ∈ menu M i r) (h₂ : (o, t₂) ∈ menu M i r) :
    t₁ = t₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  simp only [Prod.mk.injEq] at ha hb
  obtain ⟨ha_o, ha_t⟩ := ha
  obtain ⟨hb_o, hb_t⟩ := hb
  -- Both reports `a, b` induce outcome `o`, so they induce the same outcome.
  have hall : M.alloc (update r i a) = M.alloc (update r i b) := by rw [ha_o, hb_o]
  -- DSIC forces equal transfers, hence equal prices.
  rw [← ha_t, ← hb_t]
  exact hM.transfer_eq_of_alloc_eq i r a b hall

/-- The agent's quasilinear utility from a menu entry `(outcome, transfer)` at true type `θ_i`: Its
valuation of the outcome plus the transfer it would receive (money received enters with a `+`,
matching the environment's sign convention). -/
def menuUtility (i : E.Agent) (θ_i : E.Theta i) (entry : E.Outcome × ℝ) : ℝ :=
  (E.quasilinearUtility i θ_i).u entry.1 entry.2

@[simp] lemma menuUtility_def (i : E.Agent) (θ_i : E.Theta i) (entry : E.Outcome × ℝ) :
    menuUtility i θ_i entry = E.value i entry.1 θ_i + entry.2 := rfl

variable (M) in
/-- The menu entry produced by truthful reporting: The outcome and transfer the mechanism assigns
when agent `i` reports its true type `θ_i` (others fixed at `r`). It lies in the menu by
construction (it is the value at `s = θ_i`). -/
def truthfulEntry (i : E.Agent) (r : E.TypeProfile) (θ_i : E.Theta i) : E.Outcome × ℝ :=
  (M.alloc (update r i θ_i), M.transfer i (update r i θ_i))

/-- The truthful entry is a reachable menu entry. -/
lemma truthfulEntry_mem_menu (i : E.Agent) (r : E.TypeProfile) (θ_i : E.Theta i) :
    truthfulEntry M i r θ_i ∈ menu M i r :=
  ⟨θ_i, rfl⟩

/-- The menu utility of the truthful entry is the agent's ex-post utility under truthful reporting.
Definitionally these are the same quasilinear expression. -/
lemma menuUtility_truthfulEntry (i : E.Agent) (r : E.TypeProfile) (θ_i : E.Theta i) :
    menuUtility i θ_i (truthfulEntry M i r θ_i) = M.exPostUtility i (update r i θ_i) θ_i := rfl

/-- **Taxation principle, implementation form.** Under DSIC, the truthful entry maximizes the
agent's quasilinear menu utility over the posted menu, so it is an optimal entry. Hence an agent
optimizing the posted price menu can reproduce the mechanism's allocation and transfer at its true
type. This is optimality, not unique selection: A different outcome may tie the truthful utility —
see `menu_maximizer_unique` for the strict-incentive condition that fixes the choice. -/
theorem implements_menu (hM : M.IsDSIC) (i : E.Agent) (r : E.TypeProfile) (θ_i : E.Theta i) :
    IsMaxOn (menuUtility i θ_i) (menu M i r) (truthfulEntry M i r θ_i) := by
  -- Every menu entry is reached by some own-report `s`; its menu utility is the ex-post utility of
  -- reporting `s`, which DSIC bounds above by truthful reporting.
  rw [isMaxOn_iff]
  rintro _ ⟨s, rfl⟩
  -- Both sides are quasilinear `value + transfer`; reduce to the DSIC inequality at `s` vs. truth.
  change E.value i (M.alloc (update r i s)) θ_i + M.transfer i (update r i s) ≤
    menuUtility i θ_i (truthfulEntry M i r θ_i)
  rw [menuUtility_truthfulEntry]
  exact hM i r θ_i s

/-- **Posted-menu implementation, packaged.** Under DSIC the posted menu admits an optimal truthful
entry: The truthful entry lies in the menu, maximizes the agent's menu utility, and its outcome and
price are the DSIC allocation and transfer at the true type. This states implementation as the
existence of an optimal truthful entry; for uniqueness of the agent's choice (no other outcome
ties), see `menu_maximizer_unique`. -/
theorem menu_choice_eq_mechanism (hM : M.IsDSIC) (i : E.Agent) (r : E.TypeProfile)
    (θ_i : E.Theta i) :
    truthfulEntry M i r θ_i ∈ menu M i r ∧
      IsMaxOn (menuUtility i θ_i) (menu M i r) (truthfulEntry M i r θ_i) ∧
        (truthfulEntry M i r θ_i).1 = M.alloc (update r i θ_i) ∧
          (truthfulEntry M i r θ_i).2 = M.transfer i (update r i θ_i) :=
  ⟨truthfulEntry_mem_menu i r θ_i, implements_menu hM i r θ_i, rfl, rfl⟩

variable (M) in
/-- The agent's preferences **strictly separate** the mechanism's allocation at `(i, r, θ_i)`:
Every own-report inducing a different outcome than truthful reporting yields strictly lower ex-post
utility. This is the strict-incentive condition that upgrades "an optimal menu entry" to the unique
one: It rules out a misreport tying the truthful menu utility with a different outcome. -/
def StrictlySeparatesAlloc (i : E.Agent) (r : E.TypeProfile) (θ_i : E.Theta i) : Prop :=
  ∀ s : E.Theta i, M.alloc (update r i s) ≠ M.alloc (update r i θ_i) →
    M.exPostUtility i (update r i s) θ_i < M.exPostUtility i (update r i θ_i) θ_i

/-- **Taxation principle, unique implementation.** Under DSIC, if the agent's preferences strictly
separate the truthful allocation (`StrictlySeparatesAlloc`), the truthful entry is the unique
maximizer of the posted menu's utility. Hence an agent optimizing the menu chooses exactly the
mechanism's allocation and transfer at its true type — no other outcome can tie. -/
theorem menu_maximizer_unique (hM : M.IsDSIC) (i : E.Agent) (r : E.TypeProfile) (θ_i : E.Theta i)
    (hsep : StrictlySeparatesAlloc M i r θ_i)
    {e : E.Outcome × ℝ} (he : e ∈ menu M i r)
    (hmax : IsMaxOn (menuUtility i θ_i) (menu M i r) e) :
    e = truthfulEntry M i r θ_i := by
  -- `e` is reached by some own-report `s`; its menu utility is the ex-post utility of that report.
  obtain ⟨s, rfl⟩ := he
  -- `e` and the truthful entry are both maximizers, hence carry equal menu utility.
  have htruth_mem := truthfulEntry_mem_menu (M := M) i r θ_i
  have hle₁ : menuUtility i θ_i (truthfulEntry M i r θ_i) ≤
      menuUtility i θ_i (M.alloc (update r i s), M.transfer i (update r i s)) := hmax htruth_mem
  have hle₂ : menuUtility i θ_i (M.alloc (update r i s), M.transfer i (update r i s)) ≤
      menuUtility i θ_i (truthfulEntry M i r θ_i) :=
    implements_menu hM i r θ_i ⟨s, rfl⟩
  have hutil : M.exPostUtility i (update r i s) θ_i = M.exPostUtility i (update r i θ_i) θ_i :=
    le_antisymm hle₂ hle₁
  -- Equal utility forces equal outcomes: a different outcome would be strictly worse by `hsep`.
  have halloc : M.alloc (update r i s) = M.alloc (update r i θ_i) := by
    by_contra hne
    exact absurd hutil (ne_of_lt (hsep s hne))
  -- Same outcome ⇒ same price by well-definedness of the menu, so the entries coincide.
  have htransfer : M.transfer i (update r i s) = M.transfer i (update r i θ_i) :=
    hM.transfer_eq_of_alloc_eq i r s θ_i halloc
  exact Prod.ext halloc htransfer

end Econlib.MechanismDesign.Transfers.General
end
