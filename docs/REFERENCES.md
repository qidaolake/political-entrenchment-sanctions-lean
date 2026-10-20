# References cited by the formalization

Lean docstrings in this development cite sources by a local path, e.g.
`PaperRefer/MathTheory/ContractionMappingsDP-Denardo-1967.md` or
`BookRefer/NDP.md`. Those directories are **research infrastructure and are not
distributed**: they hold third-party copyrighted material — complete textbooks,
publisher PDFs, and arXiv source bundles — which cannot lawfully be
redistributed in a public artifact.

This file is the resolver. Every path a docstring cites appears below with its
bibliographic source, so a reader can obtain the reference independently. No
copyrighted content is reproduced here.

The formalization does not depend on these files: `lake build` reads only
`Sanctions/`, `lakefile.toml`, `lean-toolchain`, and mathlib. The citations are
provenance for the mathematics, not build inputs.

---

## Books (`BookRefer/…`)

| Cited as | Source |
|---|---|
| `Markov Decision Processes Discrete Stochastic Dynamic Programming (Martin L. Puterman) 1994` | Puterman, M. L. (1994). *Markov Decision Processes: Discrete Stochastic Dynamic Programming*. Wiley. |
| `NDP.md`, `NDP.pdf`, `NDP_full.txt`, `NDP_toc.txt`, `NDP_p120-130.txt` | Bertsekas, D. P., & Tsitsiklis, J. N. (1996). *Neuro-Dynamic Programming*. Athena Scientific. |
| `Recursive Methods in Economic Dynamics (Nancy L. Stokey, Robert E. Lucas Jr. etc.)` | Stokey, N. L., Lucas, R. E., with Prescott, E. C. (1989). *Recursive Methods in Economic Dynamics*. Harvard University Press. |
| `Set-Valued Analysis (J. Aubin, H. Frankowska)` | Aubin, J.-P., & Frankowska, H. (1990). *Set-Valued Analysis*. Birkhäuser. |
| `Infinite Dimensional Analysis: A Hitchhiker's Guide, Third Edition` | Aliprantis, C. D., & Border, K. C. (2006). *Infinite Dimensional Analysis: A Hitchhiker's Guide* (3rd ed.). Springer. doi:10.1007/3-540-29587-9 |
| `TOPKIS-*-1998` (six chapter extracts) | Topkis, D. M. (1998). *Supermodularity and Complementarity*. Princeton University Press. |
| `NonsmoothEquationsInOptimization-KlatteKummer-2002` | Klatte, D., & Kummer, B. (2002). *Nonsmooth Equations in Optimization*. Kluwer. |
| `Cannarsa-Sinestrari-2004_SemiconcaveFunctions` | Cannarsa, P., & Sinestrari, C. (2004). *Semiconcave Functions, Hamilton–Jacobi Equations, and Optimal Control*. Birkhäuser. |
| `Block-Coppel-1992_DynamicsInOneDimension` | Block, L. S., & Coppel, W. A. (1992). *Dynamics in One Dimension*. Lecture Notes in Mathematics 1513, Springer. |
| `Computational Stochastic Programming (Lewis Ntaimo) 2024` | Ntaimo, L. (2024). *Computational Stochastic Programming*. Springer. |

## Papers (`PaperRefer/MathTheory/…`)

| Cited as | Source |
|---|---|
| `ContractionMappingsDP-Denardo-1967` | Denardo, E. V. (1967). Contraction mappings in the theory underlying dynamic programming. *SIAM Review*, 9(2), 165–177. |
| `WeightedSupNormContractionsDP-Bertsekas-2012` | Bertsekas, D. P. (2012). Weighted sup-norm contractions in dynamic programming: a review and some new applications. MIT LIDS Report LIDS-P-2884. |
| `LipschitzValueFunctionsMDP-Hinderer-2005` | Hinderer, K. (2005). Lipschitz continuity of value functions in Markovian decision processes. *Mathematical Methods of Operations Research*, 62(1), 3–22. |
| `ContinuousStateDP-NonexpansiveApprox-Stachurski-2008` | Stachurski, J. (2008). Continuous state dynamic programming via nonexpansive approximation. *Computational Economics*, 31(2), 141–160. |
| `DifferentiabilityValueFunction-RinconZapateroSantos-2009` | Rincón-Zapatero, J. P., & Santos, M. S. (2009). Differentiability of the value function without interiority assumptions. *Journal of Economic Theory*, 144(5), 1948–1964. |
| `IntervalDominanceOrderExtensions-QuahStrulovici` | Quah, J. K.-H., & Strulovici, B. (2009). Comparative statics, informativeness, and the interval dominance order. *Econometrica*, 77(6), 1949–1992. doi:10.3982/ECTA7583 — with the unpublished *Some Extensions* companion notes. |
| `NashEquilibriumStrategicComplementarities-Vives-1990` | Vives, X. (1990). Nash equilibrium with strategic complementarities. *Journal of Mathematical Economics*, 19(3), 305–321. |
| `RationalizabilityLearningEquilibrium-MilgromRoberts-1990` | Milgrom, P., & Roberts, J. (1990). Rationalizability, learning, and equilibrium in games with strategic complementarities. *Econometrica*, 58(6), 1255–1277. |
| `SupermodularNashCompleteLattice-Zhou-1994` | Zhou, L. (1994). The set of Nash equilibria of a supermodular game is a complete lattice. *Games and Economic Behavior*, 7(2), 295–300. |
| `ConstructiveMarkovEquilibria-BalbusReffettWozny-2013` | Balbus, Ł., Reffett, K., & Woźny, Ł. (2013). A constructive study of Markov equilibria in stochastic games with strategic complementarities. *Journal of Economic Theory*, 150, 815–840. |
| `MarkovEquilibriumIntergenerationalAltruism-BalbusReffettWozny-2013` | Balbus, Ł., Reffett, K., & Woźny, Ł. (2013). Markov stationary equilibria in stochastic supermodular games with imperfect private and public information. *Dynamic Games and Applications*, 3, 187–206. |
| `StationaryMarkovianAltruisticOLG-BalbusReffettWozny-2012` | Balbus, Ł., Reffett, K., & Woźny, Ł. (2012). Stationary Markovian equilibrium in altruistic stochastic OLG models with limited commitment. *Journal of Mathematical Economics*, 48(2), 115–132. |
| `DynamicGamesInMacroeconomics-BalbusReffettWozny-monograph` | Balbus, Ł., Reffett, K., & Woźny, Ł. Dynamic games in macroeconomics. In *Handbook of Dynamic Game Theory*, Springer. |
| `LipschitzRecursiveEquilibrium-RaadWozny-2019` | Raad, R., & Woźny, Ł. (2019). On Lipschitz continuity of recursive equilibria. Working paper. |

## Papers (`PaperRefer/StochasticGames/…`, `PaperRefer/Sanctions/…`)

| Cited as | Source |
|---|---|
| `TheoryOfInternationalEconomicSanctions-KaempferLowenberg-1988` | Kaempfer, W. H., & Lowenberg, A. D. (1988). The theory of international economic sanctions: a public choice approach. *American Economic Review*, 78(4), 786–793. |
| `AppliedDynamicAnalysisIO-DoraszelskiPakes` | Doraszelski, U., & Pakes, A. (2007). A framework for applied dynamic analysis in IO. In *Handbook of Industrial Organization*, vol. 3, 1887–1966. |
| `SelfConsistentFeedbackStackelberg-BressanJiang-2020` | Bressan, A., & Jiang, Y. (2020). Self-consistent feedback Stackelberg solutions for infinite horizon stochastic games. Published version. |
| `Stationary_Strong_Stackelberg_Equilibrium_in_Discounted_Stochastic_Games` | Bucarey, V., et al. Stationary strong Stackelberg equilibrium in discounted stochastic games. |
| `ApproximateFeedbackStackelbergMultiplayer-Li-etal-2024` | Li, J., et al. (2024). Approximate feedback Stackelberg equilibria in multi-player nonlinear constrained dynamic games. |
| `StackelbergExistenceSymbolicRoutes-synthesis-2026-08` | Internal synthesis note (not third-party); summarises the existence routes surveyed above. |

Additional directories (`PoliticalEconomy/`, `SanctionsContext/`,
`SanctionsEmpirics/`, `SanctionsTheory/`, `ProofFormNorms/`) hold background
literature that informs the manuscript rather than the Lean; those works are
cited in the paper's bibliography (`paper/annote.bib`), which is the
authoritative citation list for the article.

---

## Note for maintainers

If a Lean docstring adds a new `PaperRefer/…` or `BookRefer/…` pointer, add the
matching row here in the same change. A pointer with no row is a dangling
reference in the distributed package, since the target directory is not shipped.
