\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{thesis}

\LoadClass[12pt,twoside,openright,draft]{report}

\RequirePackage{amsfonts}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{amsthm}
\ifdefined\forprint
\RequirePackage{geometry}
\RequirePackage[hidelinks]{hyperref}
\fi
\ifdefined\forweb
\RequirePackage[margin=1.25in]{geometry}
\RequirePackage[pdfborder={0 0
0},colorlinks=true,citecolor=purple,linkcolor=violet]{hyperref}
\fi
\RequirePackage{isabelle}
\RequirePackage[square,sort,comma,numbers]{natbib}
\RequirePackage{float}
\RequirePackage{graphicx}
\RequirePackage{isabelle,isabellesym}
\RequirePackage{xcolor}
\RequirePackage{xspace}

\isabellestyle{it}

% Credit: https://github.com/trvedata/crdt-isabelle/blob/master/paper/network.tex
\renewenvironment{isabelle}{%
  \medbreak\noindent\hspace{\parindent}%
  \begin{minipage}{\textwidth}% use minipage to prevent page breaks
  \begin{isabellebody}%
  \begin{tabbing}%
}{%
  \end{tabbing}%
  \end{isabellebody}%
  \end{minipage}%
  \medbreak%
}

\newcommand*{\supervisor}[1]{\gdef\@supervisor{#1}}

\bibliographystyle{abbrvnat}
\setcitestyle{numbers}

\newtheorem{definition}{Definition}[chapter]
\newtheorem{theorem}{Theorem}[chapter]
\newtheorem{example}{Example}[chapter]

\newcommand*{\TODO}[1][]{\text{\color{red} TODO {#1}}}

\newcommand*{\fst}{\ensuremath{\textsf{fst}}}
\newcommand*{\snd}{\ensuremath{\textsf{snd}}}

\newcommand*{\CRDT}{\textsf{CRDT}\xspace}
\newcommand*{\CRDTs}{\textsf{CRDTs}\xspace}
\newcommand*{\EC}{\textsf{EC}\xspace}
\newcommand*{\SEC}{\textsf{SEC}\xspace}

\makeatletter
\def\@maketitle{%
  \newpage
}

\newcommand\frontmatter{%
  \cleardoublepage
  \pagenumbering{roman}}

\newcommand\mainmatter{%
  \cleardoublepage
  \pagenumbering{arabic}}

\newcommand\backmatter{%
  \if@openright
    \cleardoublepage
  \else
    \clearpage
  \fi}

\makeatother
