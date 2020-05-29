\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{thesis}

\ifdefined\forprint
  \LoadClass[12pt,twoside,openright,letterpaper]{report}
\else
  \LoadClass[12pt,openright,a4paper]{report}
\fi

\RequirePackage[dottedtoc=true]{classicthesis}
\RequirePackage{amsfonts}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{amsthm}
\ifdefined\forprint
\RequirePackage{geometry}
\hypersetup{hidelinks}
\fi
\ifdefined\forweb
\RequirePackage[margin=1.25in]{geometry}
\hypersetup{%
  pdfborder={0 0 0},colorlinks=true,citecolor=purple,linkcolor=violet
}
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
\setcitestyle{authoryear}

\newtheorem{definition}{Definition}[chapter]
\newtheorem{theorem}{Theorem}[chapter]
\newtheorem{maxim}{Maxim}[chapter]
\newtheorem{example}{Example}[chapter]

\newcommand*{\TODO}[1][]{\text{\color{red} TODO {#1}}}

\newcommand*{\fst}{\ensuremath{\textsf{fst}}}
\newcommand*{\snd}{\ensuremath{\textsf{snd}}}

\newcommand*{\CRDT}{\textsf{CRDT}\xspace}
\newcommand*{\CRDTs}{\textsf{CRDTs}\xspace}
\newcommand*{\CC}{\textsf{CC}\xspace}
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
