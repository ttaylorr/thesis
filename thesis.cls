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
\RequirePackage{hyperref}
\RequirePackage{xcolor}

\newcommand*{\supervisor}[1]{\gdef\@supervisor{#1}}

\bibliographystyle{unsrt}

\newtheorem{definition}{Definition}[chapter]
\newtheorem{theorem}{Theorem}[chapter]

\newcommand*{\TODO}[1][]{\text{\color{red} TODO {#1}}}

\makeatletter
\def\@maketitle{%
  \newpage
}
\makeatother
