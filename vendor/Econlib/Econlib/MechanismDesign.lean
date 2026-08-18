/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Basic
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.ConvexOrder
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Optimality
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Realization
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.Basic
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.ConvexOrder
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.Cutoff
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.Experiment
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.Optimality
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Basic
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.ComplementarySlackness
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Discretization.Basic
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Discretization.DualApproximation
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Discretization.NoDualityGap
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.DualAttainment
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.ExtremeStructures
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.KRStrongDuality
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Perturbation
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.PrimalAttainment
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.StrongDuality
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Supergradient
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.WeakDuality
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Basic
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Caratheodory
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.NoInformation
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Splitting
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.StepFunction
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization.Closedness
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization.Compactness
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization.Existence
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization.MeanTests
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.Basic
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.CompositionLipschitz
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ConvexRoof
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.Differentiable
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.DifferentiableActiveSet
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.DifferentiableUniqueness
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.AuxiliaryMinimizer
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.CellDisintegration
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.CellMartingale
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.ContactFibre
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.ContactSupportPrimal
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.KernelReshuffle
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.LocalImprovement
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.MeasurableChoquet
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.SupportCell
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.JointPosteriorBridge
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.MartingaleExtension
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.MomentImage
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.OptimalDualPrice
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.OptimalDualPriceCanonical
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.OptimalDualPriceForward
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.OptimalDualPriceStructural
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.PricesForMoments
public import Econlib.MechanismDesign.Transfers.Bilateral.Environment
public import Econlib.MechanismDesign.Transfers.Bilateral.MyersonSatterthwaite
public import Econlib.MechanismDesign.Transfers.General.Allocation
public import Econlib.MechanismDesign.Transfers.General.DirectMechanism
public import Econlib.MechanismDesign.Transfers.General.Environment
public import Econlib.MechanismDesign.Transfers.General.Groves.DSIC
public import Econlib.MechanismDesign.Transfers.General.Groves.Payments
public import Econlib.MechanismDesign.Transfers.General.Groves.VCG
public import Econlib.MechanismDesign.Transfers.General.Groves.VCGProperties
public import Econlib.MechanismDesign.Transfers.General.IndirectMechanism
public import Econlib.MechanismDesign.Transfers.General.RevelationPrinciple
public import Econlib.MechanismDesign.Transfers.General.SolutionConcepts
public import Econlib.MechanismDesign.Transfers.General.StrictSeparation
public import Econlib.MechanismDesign.Transfers.General.TaxationPrinciple
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Achievable
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Environment
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.FirstPrice
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.FirstPriceBNE
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.FirstPriceGame
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.FirstPriceMechanism
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Mechanism
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Optimal
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.ReducedForm
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.RevenueEquivalence
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.RevenueIdentity
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.SecondPriceMechanism
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Envelope
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Environment
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Incentive
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Ironing
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Monotone
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.MyersonLemma
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.PaymentFormula
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueEquivalence
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueIdentity
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.VirtualValue

/-!
# Mechanism design library

This module collects Econlib's mechanism-design API. It exposes Bayesian persuasion and information
design, quasilinear direct and indirect mechanisms, Groves and VCG mechanisms, single-parameter
screening, symmetric IID auctions, and bilateral-trade impossibility results.

## Main topics

* Information design: Finite and continuous persuasion, threshold experiments, moment persuasion,
  convex-order and duality certificates, and Caratheodory/extreme-point structure.
* General transfers: Allocation environments, direct and indirect mechanisms, solution concepts,
  the revelation and taxation principles, Groves payments, VCG, DSIC, individual rationality, and
  no-deficit properties.
* Single-parameter models: Incentive compatibility, envelope and payment formulas, Myerson's lemma,
  virtual values, ironing, revenue identity, and revenue equivalence.
* Auctions and bilateral trade: First-price and second-price auction mechanisms, reduced forms,
  revenue optimality, achievable bounds, and the Myerson-Satterthwaite theorem.

## Tags

mechanism design, persuasion, transfers, auctions, screening
-/
