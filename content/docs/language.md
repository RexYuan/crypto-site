---
title: "Language"
weight: 2
# bookFlatSection: false
# bookToc: true
# bookHidden: false
# bookCollapseSection: false
# bookComments: false
# bookSearchExclude: false
---

{{< katex display >}}
\gdef{\hide}#1{}
\gdef{\exercise}{\noindent\textbf{Exercise:}}
\gdef{\todo}#1{\textbf{TODO:}{#1}}

\gdef{\mZ}{{\mathbb{Z}}}
\gdef{\mN}{{\mathbb{N}}}

\gdef{\xeightysix}{x86\_64}

\gdef{\cryptoline}{\textrm{CryptoLine}}
\gdef{\openssl}{\textrm{OpenSSL}}
\gdef{\blst}{\textrm{blst}}
\gdef{\pqclean}{\textrm{PQClean}}
\gdef{\pqmfour}{\textrm{pqm4}}
\gdef{\python}{\textrm{Python}}
\gdef{\gdb}{\textrm{gdb}}
\gdef{\ocaml}{\textrm{OCaml}}
\gdef{\opam}{\textrm{opam}}
\gdef{\boolector}{\textrm{boolector}}
\gdef{\singular}{\textrm{Singular}}
\gdef{\ubuntu}{\textrm{ubuntu}}

\gdef{\cryptolinehome}{\texttt{\\$(CL\_HOME)}}
\gdef{\itrace}{\texttt{itrace.py}}
\gdef{\tozdsl}{\texttt{to\_zdsl.py}}
\gdef{\nistzadd}{\texttt{ecp\_nistz256\_add}}
\gdef{\nistzaddgas}{\texttt{ecp\_nistz256\_add.gas}}
\gdef{\nistzaddcl}{\texttt{ecp\_nistz256\_add.cl}}
\gdef{\nistzmul}{\texttt{ecp\_nistz256\_mul\_mont}}
\gdef{\nistzmulgas}{\texttt{ecp\_nistz256\_mul\_mont.gas}}
\gdef{\nistzmulcl}{\texttt{ecp\_nistz256\_mul\_mont.cl}}


\gdef{\derefop}{\mathit{\$}}
\gdef{\deref}#1{\mathit{\$#1}}
\gdef{\wordsize}{W}
\gdef{\prog}{\mathit{prog}}
\gdef{\stmt}{\mathit{stmt}}
\gdef{\proc}{\mathit{proc}}
\gdef{\formals}{\mathit{formals}}
\gdef{\true}{\mathit{true}}
\gdef{\minusop}{-}
\gdef{\eqop}{=}
\gdef{\negop}{\sim}
\gdef{\addop}{+}
\gdef{\subop}{-}
\gdef{\mulop}{*}
\gdef{\powop}{**}
\gdef{\landop}{\mathit{/\backslash}}
\gdef{\lorop}{\mathit{\backslash/}}
\gdef{\notop}{!}
\gdef{\andop}{\mathit{\text{\&}}}
\gdef{\orop}{\mathit{|}}
\gdef{\xorop}{\mathit{\text{\textasciicircum}}}
\gdef{\ultop}{\mathit{<}}
\gdef{\uleop}{\mathit{<=}}
\gdef{\ugtop}{\mathit{>}}
\gdef{\ugeop}{\mathit{>=}}
\gdef{\sltop}{\mathit{<s}}
\gdef{\sleop}{\mathit{<=s}}
\gdef{\sgtop}{\mathit{>s}}
\gdef{\sgeop}{\mathit{>=s}}
\gdef{\iult}{\mathit{ult}}
\gdef{\iule}{\mathit{ule}}
\gdef{\iugt}{\mathit{ugt}}
\gdef{\iuge}{\mathit{uge}}
\gdef{\islt}{\mathit{slt}}
\gdef{\isle}{\mathit{sle}}
\gdef{\isgt}{\mathit{sgt}}
\gdef{\isge}{\mathit{sge}}
\gdef{\pre}{\mathit{pre}}
\gdef{\post}{\mathit{post}}
\gdef{\pred}{\mathit{pred}}
\gdef{\epred}{\mathit{epred}}
\gdef{\rpred}{\mathit{rpred}}
\gdef{\predclause}{\mathit{pred\_clause}}
\gdef{\epredclause}{\mathit{epred\_clause}}
\gdef{\rpredclause}{\mathit{rpred\_clause}}
\gdef{\iuext}{\mathit{uext}}
\gdef{\isext}{\mathit{sext}}
\gdef{\imod}{\mathit{mod}}
\gdef{\iumod}{\mathit{umod}}
\gdef{\ismod}{\mathit{smod}}
\gdef{\isrem}{\mathit{srem}}
\gdef{\ilimbs}{\mathit{limbs}}
\gdef{\eexp}{\mathit{eexp}}
\gdef{\rexp}{\mathit{rexp}}
\gdef{\instr}{\mathit{instr}}
\gdef{\imov}{\mathit{mov}}
\gdef{\iadd}{\mathit{add}}
\gdef{\iuadd}{\mathit{uadd}}
\gdef{\isadd}{\mathit{sadd}}
\gdef{\iadds}{\mathit{adds}}
\gdef{\iuadds}{\mathit{uadds}}
\gdef{\isadds}{\mathit{sadds}}
\gdef{\iaddr}{\mathit{addr}}
\gdef{\iuaddr}{\mathit{uaddr}}
\gdef{\isaddr}{\mathit{saddr}}
\gdef{\iadc}{\mathit{adc}}
\gdef{\iuadc}{\mathit{uadc}}
\gdef{\isadc}{\mathit{sadc}}
\gdef{\iadcs}{\mathit{adcs}}
\gdef{\iuadcs}{\mathit{uadcs}}
\gdef{\isadcs}{\mathit{sadcs}}
\gdef{\iadcr}{\mathit{adcr}}
\gdef{\iuadcr}{\mathit{uadcr}}
\gdef{\isadcr}{\mathit{sadcr}}
\gdef{\isub}{\mathit{sub}}
\gdef{\iusub}{\mathit{usub}}
\gdef{\issub}{\mathit{ssub}}
\gdef{\isubs}{\mathit{subs}}
\gdef{\iusubs}{\mathit{usubs}}
\gdef{\issubs}{\mathit{ssubs}}
\gdef{\isubc}{\mathit{subc}}
\gdef{\iusubc}{\mathit{usubc}}
\gdef{\issubc}{\mathit{ssubc}}
\gdef{\isubb}{\mathit{subb}}
\gdef{\iusubb}{\mathit{usubb}}
\gdef{\issubb}{\mathit{ssubb}}
\gdef{\isubr}{\mathit{subr}}
\gdef{\iusubr}{\mathit{usubr}}
\gdef{\issubr}{\mathit{ssubr}}
\gdef{\isbc}{\mathit{sbc}}
\gdef{\iusbc}{\mathit{usbc}}
\gdef{\issbc}{\mathit{ssbc}}
\gdef{\isbcs}{\mathit{sbcs}}
\gdef{\iusbcs}{\mathit{usbcs}}
\gdef{\issbcs}{\mathit{ssbcs}}
\gdef{\isbcr}{\mathit{sbcr}}
\gdef{\iusbcr}{\mathit{usbcr}}
\gdef{\issbcr}{\mathit{ssbcr}}
\gdef{\isbb}{\mathit{sbb}}
\gdef{\iusbb}{\mathit{usbb}}
\gdef{\issbb}{\mathit{ssbb}}
\gdef{\isbbs}{\mathit{sbbs}}
\gdef{\iusbbs}{\mathit{usbbs}}
\gdef{\issbbs}{\mathit{ssbbs}}
\gdef{\isbbr}{\mathit{sbbr}}
\gdef{\iusbbr}{\mathit{usbbr}}
\gdef{\issbbr}{\mathit{ssbbr}}
\gdef{\imul}{\mathit{mul}}
\gdef{\iumul}{\mathit{umul}}
\gdef{\ismul}{\mathit{smul}}
\gdef{\imuls}{\mathit{muls}}
\gdef{\iumuls}{\mathit{umuls}}
\gdef{\ismuls}{\mathit{smuls}}
\gdef{\imulr}{\mathit{mulr}}
\gdef{\iumulr}{\mathit{umulr}}
\gdef{\ismulr}{\mathit{smulr}}
\gdef{\imull}{\mathit{mull}}
\gdef{\iumull}{\mathit{umull}}
\gdef{\ismull}{\mathit{smull}}
\gdef{\imulj}{\mathit{mulj}}
\gdef{\iumulj}{\mathit{umulj}}
\gdef{\ismulj}{\mathit{smulj}}
\gdef{\isplit}{\mathit{split}}
\gdef{\ispl}{\mathit{spl}}
\gdef{\ijoin}{\mathit{join}}
\gdef{\ishl}{\mathit{shl}}
\gdef{\ishls}{\mathit{shls}}
\gdef{\ishr}{\mathit{shr}}
\gdef{\ishrs}{\mathit{shrs}}
\gdef{\isar}{\mathit{sar}}
\gdef{\isars}{\mathit{sars}}
\gdef{\icshl}{\mathit{cshl}}
\gdef{\icshr}{\mathit{cshr}}
\gdef{\icshrs}{\mathit{cshrs}}
\gdef{\iset}{\mathit{set}}
\gdef{\iclear}{\mathit{clear}}
\gdef{\inondet}{\mathit{nondet}}
\gdef{\icmov}{\mathit{cmov}}
\gdef{\ieq}{\mathit{eq}}
\gdef{\ieqmod}{\mathit{eqmod}}
\gdef{\iequmod}{\mathit{equmod}}
\gdef{\ieqsmod}{\mathit{eqsmod}}
\gdef{\ieqsrem}{\mathit{eqsrem}}
\gdef{\ineg}{\mathit{neg}}
\gdef{\iand}{\mathit{and}}
\gdef{\ior}{\mathit{or}}
\gdef{\ixor}{\mathit{xor}}
\gdef{\inot}{\mathit{not}}
\gdef{\iassert}{\mathit{assert}}
\gdef{\iassume}{\mathit{assume}}
\gdef{\ighost}{\mathit{ghost}}
\gdef{\icut}{\mathit{cut}}
\gdef{\iecut}{\mathit{ecut}}
\gdef{\ircut}{\mathit{rcut}}
\gdef{\icast}{\mathit{cast}}
\gdef{\ivpc}{\mathit{vpc}}
\gdef{\icall}{\mathit{call}}
\gdef{\inop}{\mathit{nop}}
\gdef{\iconst}{\mathit{const}}
\gdef{\iprove}{\mathit{prove}}
\gdef{\iwith}{\mathit{with}}
\gdef{\provewith}{\mathit{prove\_with}}
\gdef{\precondition}{\mathit{precondition}}
\gdef{\all}{\mathit{all}}
\gdef{\cuts}{\mathit{cuts}}
\gdef{\assumes}{\mathit{assumes}}
\gdef{\ghosts}{\mathit{ghosts}}
\gdef{\algebra}{\mathit{algebra}}
\gdef{\range}{\mathit{range}}
\gdef{\solver}{\mathit{solver}}
\gdef{\varseq}{\mathit{varseq}}
\gdef{\atom}{\mathit{atom}}
\gdef{\atomseq}{\mathit{atomseq}}
\gdef{\var}{\mathit{var}}
\gdef{\tvar}{\mathit{typed\_var}}
\gdef{\lval}{\mathit{lval}}
\gdef{\simpleconst}{\mathit{simple\_const}}
\gdef{\complexconst}{\mathit{complexy\_const}}
\gdef{\const}{\mathit{const}}
\gdef{\tconst}{\mathit{typed\_const}}
\gdef{\id}{\mathit{id}}
\gdef{\path}{\mathit{path}}
\gdef{\smt}{\mathit{smt}}
\gdef{\cas}{\mathit{cas}}
\gdef{\singularsolver}{\mathit{singular}}
\gdef{\sagesolver}{\mathit{sage}}
\gdef{\magmasolver}{\mathit{magma}}
\gdef{\mathematicasolver}{\mathit{mathematica}}
\gdef{\macaulaysolver}{\mathit{macaulay2}}
\gdef{\maplesolver}{\mathit{maple}}
\gdef{\typ}{\mathit{typ}}
\gdef{\letter}{\mathit{letter}}
\gdef{\digit}{\mathit{digit}}
\gdef{\underscore}{\mathit{underscore}}
\gdef{\uint}{\mathsf{uint}}
\gdef{\sint}{\mathsf{sint}}
\gdef{\bit}{\mathsf{bit}}
\gdef{\band}{\&\&}
{{< /katex >}}

## Introduction

$\cryptoline$ is a tool and a language for the verification of low-level
implementations of mathematical constructs.
In $\cryptoline$, users can specify two kinds of properties,
namely algebraic properties and range properties.
Algebraic properties involve equalities and modular equalities in the
integer domain while range properties involve bit-accurate variable
ranges.
$\cryptoline$ verifies algebraic properties and range properties
separately.
Verification of algebraic properties is reduced to ideal membership
queries which are solved by external computer algebra systems.
Verification of range properties is reduced to Satisfiability Modulo
Theories (SMT) queries which are solved by external SMT solvers.

## $\cryptoline$ Language

An *identifier* is a regular string started by a letter or an
underscore, followed by letters, digits, or underscores.
\\[
\id ::= (\letter \mid \underscore) [ \letter \mid \digit \mid \underscore ]
\\]

All constants and variables in $\cryptoline$ are typed.
Let $w$ be a positive integer.
$\uint w$ and $\sint w$ in $\cryptoline$ denote the types of bit-vectors
with width $w$ in the unsigned and two's complement signed
representations respectively.
The type $\uint 1$ is also written as $\bit$.
\\[
  \\begin{array}{rcl}
    \typ & ::= & \uint 1 \mid \sint 2 \mid \uint 2 \mid \sint 3 \mid
                \cdots \mid \uint w \mid \sint (w+1)
  \\end{array}
\\]

A *constant* is an integer, a binary number, a hexadecimal
number, a named constant, or arithmetic expressions over constants.

\\[
  \\begin{array}{rcl}
    \const &  ::= & \simpleconst \\\\
           & \mid & \pmb(\ \complexconst\ \pmb) \\\\
    \simpleconst &  ::= & \mZ \\\\
           & \mid & 0b[0-1]^+ \\\\
           & \mid & 0x[0-9a-fA-F]^+ \\\\
           & \mid & \pmb\derefop \id \\\\
    \complexconst &  ::= & \const \\\\
           & \mid & \pmb\minusop\ \complexconst \\\\
           & \mid & \complexconst\ \pmb\addop\ \complexconst \\\\
           & \mid & \complexconst\ \pmb\subop\ \complexconst \\\\
           & \mid & \complexconst\ \pmb\mulop\ \complexconst \\\\
           & \mid & \complexconst\ \pmb\powop\ \complexconst \\\\
    \tconst & ::= & \const @ \typ \\\\
           & \mid &  \typ\ \const
  \\end{array}
\\]

The value of a named integer $c$ is read by $\\$c$.
$\cryptoline$ supports the following arithmetic operators over
constants: unary minus (-), addition (+), subtraction (-),
multiplication (*), and exponent (**).
A *typed constant* is a constant with its type explicitly
specified.

A *variable* is an identity.
A *typed variable* is a variable with its type explicitly
specified.
An $\lval$ is either a variable or a typed variable.

\\[
  \\begin{array}{rcl}
    \var & ::= & \id \\\\
    \tvar & ::= & \var @ \typ \mid \typ\ \var \\\\
    \lval & ::= & \var \mid \tvar
  \\end{array}
\\]

The notation $t_{\circ}^*$ and $t_{\circ}^+$ respectlvey represents a
possibly empty and a non-empty sequence of $\circ$-separated $t$.

An *atom* is either a typed constant, a variable, or a typed
variable.
It is not necessary to specify the variable type explicitly in
an atom because $\cryptoline$ can infer the type automatically.
\\[
\atom ::= \tconst \mid \var \mid \tvar
\\]

An *algebraic expression* is evaluated over $\mZ$.
\\[
\\begin{array}{rclcl}
\eexp &  ::= & \simpleconst %\\\\
      & \mid & \var \\\\
      & \mid & \pmb{-}\ \eexp %\\\\
      & \mid & \eexp\ \pmb{+}\ \eexp \\\\
      & \mid & \eexp\ \pmb{-}\ \eexp %\\\\
      & \mid & \eexp\ \pmb{*}\ \eexp \\\\
      & \mid & \eexp\ \pmb{**}\ \eexp %\\\\
      & \mid & \pmb\ilimbs\ \const\ \pmb{[}\ \eexp_{\pmb,}^+\ \pmb{]} \\\\
      & \mid & \pmb{(}\ \eexp\ \pmb{)}
\\end{array}
\\]
$\ilimbs\ n\ [e_1, \ldots, e_m ]$ represents $e_1 + e_2 2^n + e_3
2^{2n} + \cdots + e_m 2^{(m-1)n}$.
A *range expression* is evaluated over bit vectors.
$\iconst\ w\ n$ is a bit-vector of width $w$ and value $n$.
$\negop$ ($\ineg$) is logical negation.
$\notop$ ($\inot$), $\andop$ ($\iand$), $\orop$ ($\ior$), $\xorop$ ($\ixor$) are respectively bit-wise
negation, bit-wise AND, bit-wise OR, and bit-wise XOR.
$\iumod$ is unsigned remainder.
$\isrem$ is 2's complement signed remainder (sign follows dividend).
$\ismod$ is 2's complement signed remainder (sign follows divisor).
$\iuext$ and $\isext$ are respectively unsigned and signed extension
operations.

\\[
\\begin{array}{rclcl}
  \rexp &  ::= & \pmb{(}\ \rexp\ \pmb{)}
  & \mid & \pmb\iconst\ \const\ \const \\\\
        & \mid & \pmb{-}\ \rexp
  & \mid & \rexp\ \pmb\addop\ \rexp \\\\
        & \mid & \rexp\ \pmb\subop\ \rexp
  & \mid & \rexp\ \pmb\mulop\ \rexp \\\\
        & \mid & \pmb\negop\ \rexp
  & \mid & \pmb\ineg\ \rexp \\\\
        & \mid & \pmb\notop\ \rexp
  & \mid & \pmb\inot\ \rexp \\\\
        & \mid & \rexp\ \pmb\andop\ \rexp
  & \mid & \pmb\iand\ \rexp\ \rexp \\\\
        & \mid & \rexp\ \pmb\orop\ \rexp
  & \mid & \pmb\ior\ \rexp\ \rexp \\\\
        & \mid & \rexp\ \pmb\xorop\ \rexp
  & \mid & \pmb\ixor\ \rexp\ \rexp \\\\
        & \mid & \pmb\iumod\ \rexp\ \rexp
  & \mid & \pmb\isrem\ \rexp\ \rexp \\\\
        & \mid & \pmb\ismod\ \rexp\ \rexp
  & \mid & \pmb\ilimbs\ \const\ \pmb[\ \rexp_{\pmb,}^+\ \pmb] \\\\
        & \mid & \pmb\iuext\ \rexp\ \const
  & \mid & \pmb\isext\ \rexp\ \const \\\\
\\end{array}
\\]

A *predicate* is represented by an algebraic predicate and a range predicate.
\\[
\\begin{array}{rclcl}
\pred &  ::= & \pmb\true
      & \mid & \epred\ \pmb\band\ \rpred
\\end{array}
\\]
An *algebraic predicate* is evaluated over the integer domain.
$e_1 = e_2$ ($\ieq\ e_1\ e_2$) is an equality over algebraic
expressions.
$e_1 = e_2\ (\imod\ [m_1, \ldots, m_n])$ ($\ieqmod\ e_1\ e_2$ $[m_1,
\ldots, m_n]$) is a modular equality.
$p_1\ \landop\ p_2$ ($\iand\ p_1\ p_2$) is a logical conjunction of
$p_1$ and $p_2$.
The conjunction of a sequence of algebraic predicates $e_1, \ldots,
e_n$ is written as $\landop\ [e_1, \ldots, e_n]$ ($\iand\ [e_1, \ldots,
e_n]$).
\\[
\\begin{array}{rclcl}
  \epred &  ::= & \pmb(\ \epred\ \pmb)
  & \mid & \pmb\true \\\\
         & \mid & \eexp\ \pmb\eqop\ \eexp
  & \mid & \pmb\ieq\ \eexp\ \eexp \\\\
         & \mid & \eexp\ \pmb\eqop\ \eexp\ \pmb(\ \pmb\imod\ [\eexp_{\pmb,}^+]\ \pmb)
  & \mid & \pmb\ieqmod\ \eexp\ \eexp\ [ \eexp_{\pmb,}^+ ] \\\\
         & \mid & \epred\ \pmb\landop\ \epred
  & \mid & \pmb\iand\ \epred\ \epred \\\\
         & \mid & \pmb\landop\ \pmb[\ \epred_{\pmb,}^+\ \pmb]
  & \mid & \pmb\iand\ \pmb[\ \epred_{\pmb,}^+\ \pmb] \\\\
\\end{array}
\\]
A *range predicate* specifies the ranges of variables.
$\cryptoline$ offers comparisons such as equality ($\eqop$), modular
equalities ($\iequmod$, $\ieqsmod$, $\ieqsrem$), unsigned less than
($\ultop$), unsigned less than or equal to ($\uleop$), unsigned
greater than ($\ugtop$), unsigned greater than or equal to ($\ugeop$),
signed less than ($\sltop$), signed less than or equal to ($\sleop$),
signed greater than ($\sgtop$), and signed greater than or equal to
($\sgeop$).
\\[
\\begin{array}{rclcl}
  \rpred &  ::= & \pmb{(}\ \rpred\ \pmb{)}
  & \mid & \pmb\true \\\\
         & \mid & \rexp\ \pmb\eqop\ \rexp
  & \mid & \pmb\ieq\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\eqop\ \rexp\ \pmb(\ \iumod\ \rexp\ \pmb)
  & \mid & \pmb\iequmod\ \rexp\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\eqop\ \rexp\ \pmb(\ \ismod\ \rexp\ \pmb)
  & \mid & \pmb\ieqsmod\ \rexp\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\eqop\ \rexp\ \pmb(\ \isrem\ \rexp\ \pmb)
  & \mid & \pmb\ieqsrem\ \rexp\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\ultop\ \rexp
  & \mid & \pmb\iult\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\uleop\ \rexp
  & \mid & \pmb\iule\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\ugtop\ \rexp
  & \mid & \pmb\iugt\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\ugeop\ \rexp
  & \mid & \pmb\iuge\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\sltop\ \rexp
  & \mid & \pmb\islt\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\sleop\ \rexp
  & \mid & \pmb\isle\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\sgtop\ \rexp
  & \mid & \pmb\isgt\ \rexp\ \rexp \\\\
         & \mid & \rexp\ \pmb\sgeop\ \rexp
  & \mid & \pmb\isge\ \rexp\ \rexp \\\\
         & \mid & \pmb\negop \rpred
  & \mid & \pmb\ineg \rpred \\\\
         & \mid & \rpred\ \pmb{\landop}\ \rpred
  & \mid & \pmb{\iand}\ \rpred\ \rpred \\\\
         & \mid & \rpred\ \pmb{\lorop}\ \rpred
  & \mid & \pmb{\ior}\ \rpred\ \rpred \\\\
         & \mid & \pmb{\landop}\ \pmb{[}\ \rpred_{\pmb,}^+\ \pmb{]}
  & \mid & \pmb{\iand}\ \pmb{[}\ \rpred_{\pmb,}^+\ \pmb{]} \\\\
         & \mid & \pmb{\lorop}\ \pmb{[}\ \rpred_{\pmb,}^+\ \pmb{]}
  & \mid & \pmb{\ior}\ \pmb{[}\ \rpred_{\pmb,}^+\ \pmb{]}
\\end{array}
\\]

There are numerous *instructions* supported by $\cryptoline$.
$\imov\ x\ a$ assigns destination variable $x$ by the value of the
source atom $a$.
$\icmov\ x\ c\ a_1\ a_2$ assigns destination variable $x$ by the value of the
source atom $a_1$ if the condition bit $c$ is $1$, and otherwise by
the value of the source atom $a_2$.
$\iadd\ x\ a_1\ a_2$ assigns $x$ by the addition of the source atoms
$a_1$ and $a_2$.
Note that $\iadd$ may overflow.
$\iadds\ c\ x\ a_1\ a_2$ assigns $x$ by the addition of the source atoms
$a_1$ and $a_2$ with carry bit $c$ set.
$\iadc\ x\ a_1\ a_2\ y$ assigns $x$ by the addition of the carry bit $y$
and the source atoms $a_1$ and $a_2$.
$\iadcs$ is the same as $\iadc$ except the carry bit is set.
There are also instructions $\isub$ for subtraction; $\isubc$, $\isbc$
and $\isbcs$ for subtraction with carry; $\isubb$, $\isbb$, and
$\isbbs$ for subtraction with borrow.
$\imul$ and $\imuls$ are half multiplication operations.
The differenace is that $\imuls$ sets the carry bit if the
multiplication under- or over-flow.
$\imull$ is full multiplication with results split into high part and
low part.
$\imulj$ is also full multiplication without splitting the results.
$\inondet$ assigns a variable by a nondeterministic value.
$\iset\ x$ assigns the bit variable $x$ by $1$ while $\iclear\ x$
assigns the bit variable $x$ by $0$.
$\ishl x a n$ shifts the source atom $a$ left by $n$ and stores the
results in $x$.
$\ishls o x a n$ is the same as $\ishls x a n$ except that the bits
shifted out are stored in $o$.
$\ishr x a n$ shifts the source atom $a$ right logically by $n$ and
stores the results in $x$.
$\ishrs x o a n$ is the same as $\ishr x a n$ except that the bits
shifted out are stored in $o$.
$\isar$ and $\isars$ are the same as $\ishr$ and $\ishrs$ respectively
except that the right shift is arithmetic.
$\icshl x_h x_l a_1 a_2 n$ concatenates the source atoms $a_1$ (high
bits) and $a_2$ (low bits), shifts the concatenation left by $n$,
stores the high bits of the shifted concatenation in $x_h$, and stores
the low bits shifted right by $n$ in $x_l$.
$\icshr x_h x_l a_1 a_2 n$ concatenates the source atoms $a_1$ (high
bits) and $a_2$ (low bits), shifts the concatenation right logically
by $n$, stores the high bits of the shifted concatenation in $x_h$,
and stores the low bits in $x_l$.
$\icshr x_h x_l o a_1 a_2 n$ is the same as $\icshr x_h x_l a_1 a_2 n$
except that the bits shifted out are stored in $o$.
$\ispl x_h x_l a n$ splits the source atom $a$ at position $n$, stores
the high bits in $x_h$, and stores the low bits in $x_l$.
$\isplit$ is the same as $\ispl$ except that the high bits and the low
bits are extended to the size of $a$.
While the low bits are always zero extended, the high bits are sign
extended if $a$ is signed and otherwise zero extended.
$\ijoin x a_1 a_2$ assigns $x$ by the concatenation of the source
atoms $a_1$ (high bits) and $a_2$ (low bits).
$\iand$, $\ior$, $\inot$, and $\ixor$ are bit-wise operations.
$\icast t x a$ assigns $x$ by the source atom $a$ casted to the type
$t$.
$\ivpc t x a$ is the same as $\icast t x a$ except that the integer
interpretation of $x$ must be the same as the integer interpretation
of $a$.
$\iassert$ tells $\cryptoline$ to verify the specified predicate.
$\iassume$ tells $\cryptoline$ to assume the specified predicate.
$\icut\ e\ \band\ r$ is an alias of one $\iecut\ e$ followed by a
$\ircut\ r$.
For $\iecut$, $\cryptoline$ verifies the specified algebraic predicate
and starts afresh with the predicate assumed when verifying algebraic
properties.
Similarly for $\ircut$, $\cryptoline$ verifies the specified range
predicate and starts afresh with the predicate assumed when verifying
range properties.
$\ighost$ can introduce logical variables that must only be used in
specifications such as $\iassert$, $\iassume$, $\icut$, $\iecut$,
$\ircut$, and postconditions.
The predicate in a $\ighost$ instruction is always assumed.
$\icall\ p\ (a_1, a_2, \ldots, a_n)$ executes a defined procedure $p$
with arguments $a_1, a_2, \ldots, a_n$.

\\[
\\begin{array}{rclcl}
  \instr &  ::= & \pmb\imov\ \lval\ \atom
         & \mid & \pmb\icmov\ \lval\ \lval\ \atom\ \atom \\\\
         & \mid & \pmb\iadd\ \lval\ \atom\ \atom
         & \mid & \pmb\iadds\ \lval\ \lval\ \atom\ \atom \\\\
         & \mid & \pmb\iadc\ \lval\ \atom\ \atom\ \var
         & \mid & \pmb\iadcs\ \lval\ \lval\ \atom\ \atom\ \var \\\\
         & \mid & \pmb\isub\ \lval\ \atom\ \atom \\\\
         & \mid & \pmb\isubc\ \lval\ \lval\ \atom\ \atom
         & \mid & \pmb\isubb\ \lval\ \lval\ \atom\ \atom \\\\
         & \mid & \pmb\isbc\ \lval\ \atom\ \atom\ \var
         & \mid & \pmb\isbcs\ \lval\ \lval\ \atom\ \atom\ \var \\\\
         & \mid & \pmb\isbb\ \lval\ \atom\ \atom\ \var
         & \mid & \pmb\isbbs\ \lval\ \lval\ \atom\ \atom\ \var \\\\
         & \mid & \pmb\imul\ \lval\ \atom\ \atom
         & \mid & \pmb\imuls\ \lval\ \lval\ \atom\ \atom \\\\
         & \mid & \pmb\imull\ \lval\ \lval\ \atom\ \atom
         & \mid & \pmb\imulj\ \lval\ \atom\ \atom \\\\
         & \mid & \pmb\inondet\ \lval \\\\
         & \mid & \pmb\iset\ \lval
         & \mid & \pmb\iclear\ \lval \\\\
         & \mid & \pmb\ishl\ \lval\ \atom\ \const
         & \mid & \pmb\ishls\ \lval\ \lval\ \atom\ \const \\\\
         & \mid & \pmb\ishr\ \lval\ \atom\ \const
         & \mid & \pmb\ishrs\ \lval\ \lval\ \atom\ \const \\\\
         & \mid & \pmb\isar\ \lval\ \atom\ \const
         & \mid & \pmb\isars\ \lval\ \lval\ \atom\ \const \\\\
         & \mid & \pmb\icshl\ \lval\ \lval\ \atom\ \atom\ \const \\\\
         & \mid & \pmb\icshr\ \lval\ \lval\ \atom\ \atom\ \const
         & \mid & \pmb\icshrs\ \lval\ \lval\ \lval\ \atom\ \atom\ \const \\\\
         & \mid & \pmb\ispl\ \lval\ \lval\ \atom\ \const
         & \mid & \pmb\isplit\ \lval\ \lval\ \atom\ \const \\\\
         & \mid & \pmb\ijoin\ \lval\ \lval\ \atom\ \const \\\\
         & \mid & \pmb\iand\ \lval\ \atom\ \atom
         & \mid & \pmb\ior\ \lval\ \atom\ \atom \\\\
         & \mid & \pmb\ixor\ \lval\ \atom \atom
         & \mid & \pmb\inot\ \lval\ \atom \\\\
         & \mid & \pmb\icast\ \typ\ \lval\ \atom
         & \mid & \pmb\ivpc\ \typ\ \lval\ \atom \\\\
         & \mid & \pmb\iassert\ \pred
         & \mid & \pmb\iassume\ \pred \\\\
         & \mid & \pmb\icut\ \predclause
         & \mid & \pmb\iecut\ \epredclause \\\\
         & \mid & \pmb\ircut\ \rpredclause
         & \mid & \pmb\ighost\ \tvar_{\pmb,}^+\ \pmb{:}\ \pred \\\\
         & \mid & \pmb\icall\ \id\ \pmb{(}\ \atom_{\pmb,}^* \pmb{)}
  & \mid & \pmb\inop
\\end{array}
\\]

Instructions $\iadd$, $\iadds$, $\iadc$, $\iadcs$, $\isub$, $\isubc$,
$\isubb$, $\isbc$, $\isbcs$, $\isbb$, $\isbbs$, $\imul$, $\imuls$,
$\imull$, $\imulj$, $\isplit$, and $\ispl$ also have specific unsigned
and signed versions with prefix "u" or "s".
For example, $\iuadd$ and $\isadd$ are respectively unsigned and
signed versions of $\iadd$.

Sometimes a predicate has to be proved with facts that have been cut off.
$\cryptoline$ offers the specification of hints required to prove a predicate.

\\[
\\begin{array}{rclcl}
  \predclause &  ::= & \true %\\\\
              & \mid & \epredclause\ \pmb{\\&\\&}\ \rpredclause \\\\
  \epredclause &  ::= & \epred %\\\\
              & \mid & \epred\ \pmb\iprove\ \pmb\iwith\ \pmb[
                       \provewith_{\pmb,}^+ \pmb] \\\\
              & \mid & \epredclause_{\pmb,}^+ \\\\
  \rpredclause &  ::= & \rpred %\\\\
              & \mid & \rpred\ \pmb\iprove\ \pmb\iwith\ \pmb[
                       \provewith_{\pmb,}^+ \pmb]\\\\
              & \mid & \rpredclause_{\pmb,}^+ \\\\
  \cas &  ::= & \pmb\singularsolver
              & \mid & \pmb\sagesolver \\\\
              & \mid & \pmb\magmasolver
              & \mid & \pmb\mathematicasolver \\\\
              & \mid & \pmb\macaulaysolver
              & \mid & \pmb\maplesolver \\\\
  \provewith &  ::= & \pmb\precondition
             & \mid & \pmb\all\ \pmb\cuts \\\\
             & \mid & \pmb\all\ \pmb\assumes
             & \mid & \pmb\all\ \pmb\ghosts \\\\
             & \mid & \pmb\cuts\ \pmb[ \mN_{\pmb,}^+ \pmb]
             & \mid & \pmb\algebra\ \pmb\solver\ \cas \\\\
             & \mid & \pmb\algebra\ \pmb\solver\ \pmb\smt\pmb:\path
             & \mid & \pmb\range\ \pmb\solver\ \path
\\end{array}
\\]

Note that the indices of $\iecut$ and $\ircut$ are numbered separately
(starting from 0).
When verifying algebraic properties, $\ircut$ instructions are
ignored.
When verifying range properties, $\iecut$ instructions are
ignored.
For example, consider the following program.

```
mov x 15@uint16;
ecut x = 15;
mov y 3@uint16;
cut y = 3 && and [x = 15@16, y = 3@16];
add z x y;
rcut z = 18@16;
```

If we want to prove $e\ \provewith\ [\cuts [1]]\ \band\ r\ \provewith
[\cuts [1]]$, then $y = 3$ will be assumed when proving the algebraic
property $e$ while $z = 18@16$ will be assumed when proving the range
property $r$.

A *procedure* is a parameterized program together with its
specification (precondition and postcondition).

\\[
\proc ::= \pmb\proc\ \id\ \pmb{(}\ \formals\ \pmb{)} = \pmb\\{\ \pre\ \pmb\\}\ \prog\ \pmb\\{\ \post\ \pmb\\}
\\]

The *formal parameters* of a procedure may be separated by a
semicolon into *inout} and \emph{out* variables.

\\[
\formals ::= \tvar_{\pmb,}^* \mid \tvar_{\pmb,}^*
\ \pmb{;}\ \tvar_{\pmb,}^*
\\]

Variables before the semicolon are inout variables while variables
after the semicolon are out variables.
Formal parameters without a semicolon are all inout variables.
The difference between inout and out variables is that when calling a
procedure, actual parameters of the inout formal variables must be
defined but this is not required for the actual parameters of the out
formal variables.
However, this does not mean that an out variable can be read before
initialized.
Every variable must be initialized before reading its value.
A *precondition* is a predicate.
\\[
\pre ::= \pred
\\]
A *postcondition* is a predicate clause.
\\[
\post ::= \predclause
\\]

A *statement* is a declaration of a procedure or a named integer.
\\[
\\begin{array}{rclcl}
\stmt &  ::= & \proc %\\\\
      & \mid & \pmb\iconst\ \id\ \pmb\eqop\ \const
\\end{array}
\\]

A *program* is a sequence of semicolon separated statements.
The entry point of the program is the *main* procedure.
Other procedures called in main are inlined.
\\[
\prog ::= \stmt_{\pmb;}^+
\\]
