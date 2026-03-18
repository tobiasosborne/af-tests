# LaTeX Conversion Template Instructions

## STRICT RULES

1. **ONLY convert actual Lean code** - NO comments allowed
2. Skip all lines starting with `--` (single-line comments)
3. Skip all content between `/-` and `-/` (block comments)
4. Skip import statements (not mathematical content)
5. Skip `open`, `namespace`, `section`, `end` statements

## What to Convert

Convert these Lean constructs to LaTeX:

### Definitions
```lean
def foo (x : A) : B := expr
```
becomes:
```latex
\begin{definition}[foo]
Let $x : A$. Define $\mathsf{foo}(x) : B$ by
\[ \mathsf{foo}(x) \defas \text{[expression]} \]
\end{definition}
```

### Theorems/Lemmas
```lean
theorem bar (h : P) : Q := by ...
```
becomes:
```latex
\begin{theorem}[bar]
If $P$, then $Q$.
\end{theorem}
```

### Structures/Classes
```lean
structure Foo where
  field1 : Type1
  field2 : Type2
```
becomes:
```latex
\begin{definition}[Foo]
A \textbf{Foo} consists of:
\begin{itemize}
  \item $\mathsf{field1} : \text{Type1}$
  \item $\mathsf{field2} : \text{Type2}$
\end{itemize}
\end{definition}
```

### Instances
```lean
instance : SomeClass Foo where ...
```
becomes:
```latex
\begin{proposition}
$\mathsf{Foo}$ is an instance of $\mathsf{SomeClass}$.
\end{proposition}
```

## Symbol Translations

| Lean | LaTeX |
|------|-------|
| `jmul a b` | `$a \jmul b$` |
| `jsq a` | `$\jsq{a}$` |
| `jpow a n` | `$\jpow{a}{n}$` |
| `jone` | `$\jone$` |
| `L a` | `$\Lop{a}$` |
| `U a` | `$\Uop{a}$` |
| `PeirceSpace e λ` | `$\Peirce{e}{\lambda}$` |
| `ℝ` | `$\R$` |
| `ℕ` | `$\N$` |
| `ℂ` | `$\C$` |
| `→` | `$\to$` |
| `∀` | `$\forall$` |
| `∃` | `$\exists$` |
| `∈` | `$\in$` |
| `⊆` | `$\subseteq$` |
| `≤` | `$\le$` |
| `≥` | `$\ge$` |
| `≠` | `$\ne$` |
| `∧` | `$\land$` |
| `∨` | `$\lor$` |
| `¬` | `$\lnot$` |
| `⁻¹` | `$^{-1}$` |
| `²` | `$^2$` |
| `•` | `$\cdot$` (scalar mult) |
| `∘ₗ` | `$\circ$` (composition) |
| `⊔` | `$\sqcup$` |
| `⊓` | `$\sqcap$` |
| `⊤` | `$\top$` |
| `⊥` | `$\bot$` |

## Type Translations

| Lean Type | LaTeX |
|-----------|-------|
| `J` (Jordan algebra) | $J$ |
| `Submodule ℝ J` | submodule of $J$ |
| `J →ₗ[ℝ] J` | $\R$-linear map $J \to J$ |
| `Prop` | proposition |
| `Type*` | type |

## Output Format

Each .tex file should:
1. NOT have `\documentclass` or preamble (will be \input'd)
2. Start with `\section{Filename}`
3. Have clear theorem/definition environments
4. Group related definitions together
5. Use `\subsection{}` for major groupings if file is large

## Example Output

```latex
\section{Basic}

\begin{definition}[JordanAlgebra]
A \textbf{Jordan algebra} over $\R$ is a real vector space $J$ equipped with:
\begin{itemize}
  \item A bilinear product $\jmul : J \times J \to J$
  \item An identity element $\jone \in J$
\end{itemize}
satisfying:
\begin{enumerate}
  \item (Commutativity) $a \jmul b = b \jmul a$
  \item (Jordan identity) $(a \jmul b) \jmul \jsq{a} = a \jmul (b \jmul \jsq{a})$
  \item (Identity) $\jone \jmul a = a$
\end{enumerate}
\end{definition}

\begin{definition}[jsq]
The \textbf{Jordan square} of $a \in J$ is:
\[ \jsq{a} \defas a \jmul a \]
\end{definition}

\begin{lemma}[jmul\_comm]
For all $a, b \in J$: $a \jmul b = b \jmul a$.
\end{lemma}
```
