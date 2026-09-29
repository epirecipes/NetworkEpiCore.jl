# API reference

The generic functions below are stubs or fallbacks that EdgeBasedModels, NodeBasedModels and
NetworkOutbreaks extend. Their docstrings describe each package's methods. The methods defined in
the package extensions (Symbolics, Catalyst, ModelingToolkitBase, Graphs) are documented on
the generic functions they extend.

## Shared generic functions

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["NetworkEpiCore.jl", "generics.jl"]
```

## Models: `ContactModel`, rates, typing, canned models, equivalence, transforms

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["ir/types.jl", "ir/reaction_data.jl", "ir/rates.jl", "ir/typing.jl", "ir/canned.jl",
           "ir/equivalence.jl", "ir/transforms.jl"]
```

## Networks and degree distributions

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["networks/degrees.jl", "networks/multivariate.jl", "networks/descriptors.jl"]
```

## Seeding

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["seeding.jl"]
```

## Composition: open models, gluing, stratification

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["composition/open.jl", "composition/stratify.jl"]
```

## Thresholds: R₀, the next-generation matrix, growth rate, final size

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["analysis/ngm.jl"]
```

## Morphisms

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["morphisms.jl"]
```

## Scenarios

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["scenarios/types.jl", "scenarios/canonical_text.jl", "scenarios/registry.jl",
           "scenarios/canonical.jl"]
```

## Validation: summaries, comparison, plots

```@autodocs
Modules = [NetworkEpiCore]
Pages   = ["validation/summary.jl", "validation/compare.jl", "recipes.jl"]
```

## Index

```@index
Modules = [NetworkEpiCore]
```
