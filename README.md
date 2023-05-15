# IISER Pune Type Theory Talks

A series of six lectures at the IISER Pune mathematics department giving a broad overview of type theory and interactive theorem provers.

## Using this repository

The `TypeTheoryTalks` folder of this repository contains the `Lean4` code used in the lectures. There are a few options to interact with this code yourself.

### Via local installation

Local installation is the best way, though it is a bit involved. First install `Lean4` following [these instructions](https://leanprover.github.io/lean4/doc/quickstart.html).

Next, run the following command from a terminal opened in a suitable folder (for Linux machines):

```bash
git clone https://github.com/0art0/IISER-Pune-Type-Theory-Talks.git
```

Note that this step requires [git](https://git-scm.com/) to be installed locally. On other operating systems, the code can be downloaded as a `.zip` file from [this link](https://github.com/0art0/IISER-Pune-Type-Theory-Talks/archive/refs/heads/main.zip). 

To complete the set-up, go to the project folder (presumably called `IISER-Pune-Type-Theory-Talks`) and run the following command from a terminal:

```bash
lake exe cache get
```

To finally experiment with the code, open the main directory of the project folder in the VS Code editor and click on any of the files in the `TypeTheoryTalks` sub-folder.

### Via GitPod

To run the code via GitPod, just click on this link: [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/0art0/IISER-Pune-Type-Theory-Talks). 

This opens up a session in a browser window and does not require any local installation. It may take a while to load the first time.

### Via GitHub Codespaces

GitHub Codespaces are another way of accessing this code without any local installation. Go to the [project's homepage on GitHub](https://github.com/0art0/IISER-Pune-Type-Theory-Talks) and click on `<>Code > Codespaces > Create codespace on main` (see image).

![GitHub CodeSpaces](./img/codespaces.png?raw=true "codespaces installation")

The session may take a while to load.

## Schedule

- 15.05.2023 : An introduction to type theory and interactive theorem provers
- 17.05.2023 : Propositions as Types
- 19.05.2023 : Using `Lean4` as an interactive theorem prover
- 22.05.2023 : Inductive types - I
- 24.05.2023 : Inductive types - II
- 26.05.2023 : Using `Lean4` as a programming language

## Resources

- [Theorem Proving in Lean4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [The Natural Number Game](https://adam.math.hhu.de/#/g/hhu-adam/NNG4)
- [The Lean Zulip Chat](https://leanprover.zulipchat.com/)
- [The Homotopy Type Theory book (Chapter 1)](https://homotopytypetheory.org/book/)
- [Functional Programming in Lean4](https://leanprover.github.io/functional_programming_in_lean/)