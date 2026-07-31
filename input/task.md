Please read the paper source `main.tex`and `HanGuoNiu.pdf`.

NOTE ON CHARACTERS. This file is deliberately written in plain ASCII: ">=" for
"at least", "->" for arrows, "sum"/"prod" for the operators, "Z_{3,b}",
"q^{-1}", "Ihat" for the supernomial, etc. This avoids the mojibake (garbled
characters such as "aEUR" or accented capitals) that appears when a Unicode
document is viewed through a tool that assumes a non-UTF-8 encoding. Unicode
does NOT harm the Lean compiler (Lean 4 is fully Unicode-aware and Mathlib uses
symbols like the sum operator and the integers glyph freely), but it does
garble in some editors, diff viewers, terminals, and clipboards. Keeping the
task file ASCII makes it render identically everywhere. The Lean source you
produce MAY use Unicode as usual; only this task document is constrained.

You are required to formalize and verify the following statement in Lean:

Theorem~\ref{thm:support-dominance}, Corollary~\ref{cor:half-line}, and Theorem~\ref{thm:canonical-reduction}.