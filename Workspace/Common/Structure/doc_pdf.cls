\ProvidesClass{doc_pdf}

\LoadClass[]{report}

\usepackage{graphicx}
\usepackage{caption}
\usepackage{hyperref}
\usepackage{titlepic}
\usepackage{listings}
\usepackage{color}
\usepackage{tabulary}
\usepackage{array}
\usepackage[ddmmyyyy]{datetime}
\usepackage{lipsum}

\usepackage[dvipsnames]{xcolor}
\usepackage{soul}
\usepackage{titling}
\usepackage{float}
\usepackage{enumitem}
\usepackage{fancyhdr}

\definecolor{dkgreen}{rgb}{0,0.6,0}
\definecolor{gray}{rgb}{0.5,0.5,0.5}
\definecolor{mauve}{rgb}{0.58,0,0.82}
%
\newcolumntype{X}[1]{>{\raggedright\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}	\newcolumntype{Y}[1]{>{\centering\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}
\newcolumntype{Z}[1]{>{\raggedleft\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}
%
\newcommand{\centeredBlock}[1]{
	\begin{center}
		#1
	\end{center}
}

\newcommand{\paragraphnewline}[1]{\paragraph{#1}\mbox{}\\}
\renewcommand{\listfigurename}{Figure Contents}
\newcommand{\subscript}[2]{$#1 _ #2$}
\newcommand{\configureJava}{%
	\lstset{frame=tb,%
		language=Java,
		aboveskip=3mm,
		belowskip=3mm,
		showstringspaces=false,
		columns=flexible,
		basicstyle={\small\ttfamily},
		numbers=none,
		numberstyle=\tiny\color{gray},
		keywordstyle=\color{blue},
		commentstyle=\color{dkgreen},
		stringstyle=\color{mauve},
		breaklines=true,
		breakatwhitespace=true,
		tabsize=3
	}
}
\newcommand{\enableCodeLineNumbers}{\lstset{numbers=left}}
\newcommand{\disableCodeLineNumbers}{\lstset{numbers=none}}
%
\newcommand{\PowerEnJoy}[0]{\mbox{\emph{PowerEnJoy}}}

\newcommand{\setDepth}[1]{\setcounter{tocdepth}{#1}\setcounter{secnumdepth}{#1}}
\newcommand{\itemBold}[1]{\item\textbf{#1:}}
\newcommand{\unbreakableBlock}[1]{
	\begin{minipage}{\linewidth}% Following stays together
		#1
	\end{minipage}
}
\newcommand{\unbreakableCenteredBlock}[1]{\unbreakableBlock{\centeredBlock{#1}}}
\newcommand{\unbreakableCenteredBlockSpaced}[2]{%
	\unbreakableCenteredBlock{%
		\vspace{#2}
			#1
		\vspace{#2}
	}
}
\newcommand{\unbreakableItem}[1]{\unbreakableBlock{\item #1}}
\newcommand{\showPercentImage}[5]{%
	\unbreakableCenteredBlockSpaced{%
		\includegraphics[width=#3\textwidth,keepaspectratio=true]{#1}
		\captionof{figure}{#2}
    \label{#4}
	}{#5}
}
\newcommand{\showHeightImage}[4]{%
	\unbreakableCenteredBlockSpaced{%
		\includegraphics[height=#3,keepaspectratio=true]{#1}
		\captionof{figure}{#2}
    \label{#4}
	}{0.5em}
}

\newcommand{\showImage}[3]{\showPercentImage{#1}{#2}{1}{#3}{0.5em}}
\setDepth{4}
\hypersetup{%
	colorlinks=true, %set true if you want colored links
	linktoc=all,     %set to all if you want both sections and subsections linked
	linkcolor=black,
	urlcolor=blue
}
\author{Redaelli Marco 877622 \and Zanoli Francesco 877471}
\date{\today}
\newcommand{\titleSubtitle}[2]{\title{#1 \\ \vspace{1cm} \large{#2}}}
\newcommand{\titleToc}{\maketitle\newpage\tableofcontents\listoffigures}
\newcommand{\blueHref}[2]{\hypersetup{linkcolor=blue}\hyperref[#1]{#2}\hypersetup{linkcolor=black}}

\pretitle{
  \begin{center}
 \includegraphics[width=6cm]{../Common/Resources/PoliLogo.png}
 \\
 }
\posttitle{\end{center}}

\newcommand{\pageHeader}[1]{\pagestyle{fancy}\fancyhf{}\rhead{Chapter \thechapter}\lhead{#1}\fancyfoot[CE,CO]{\thepage}}
