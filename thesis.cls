\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{thesis}

\LoadClass[12pt]{book}

\RequirePackage{amsfonts}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{amsthm}
\RequirePackage[margin=1in]{geometry}
\RequirePackage{isabelle}
\RequirePackage[square,sort,comma,numbers]{natbib}
\RequirePackage{float}
\RequirePackage{graphicx}
\RequirePackage{isabelle,isabellesym}
\RequirePackage{hyperref}
\RequirePackage{xcolor}

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
\newtheorem{example}{Example}[chapter]

\newcommand*{\TODO}[1][]{\text{\color{red} TODO {#1}}}

\makeatletter
\def\@maketitle{%
  \newpage
}
\makeatother
