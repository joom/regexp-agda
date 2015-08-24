\documentclass{scrartcl}

\def\textmu{}

%include agda.fmt

\begin{document}

We start with the module header:
\begin{code}
module Report where
\end{code}

After we import the necessary modules, we can define the function.

\begin{code}
intrinsic : (r : StdRegExp)
          → (s : List Char)
          → (k : List StdRegExp)
          → Maybe (Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k }))
\end{code}

\end{document}
