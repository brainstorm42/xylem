# Mathematics learning and teaching resources

Use these resources to connect equations to pictures, physical systems and questions you can investigate. The collection brings together interactive notebooks, animation tools, proof-linked learning workflows and reusable teaching materials. It favors inspectable sources and explanations that readers can check, adapt and discuss.

**Edition:** v0.1.0  
**Last reviewed:** October 8, 2026

## Start here

- **Explore a mathematical idea:** pair [marimo](#marimo) with a worked [python-control example](#python-control).
- **Understand a visual argument:** study the scene code in [3Blue1Brown's video collection](#3blue1brown-video-sources), then explore [TheoremExplainAgent](#theoremexplainagent) or [Code2Video](#code2video).
- **Investigate a proof:** use the [lean4-skills learning workflow](#lean4-skills) to connect questions, examples and formal statements.
- **Build a reusable lesson:** explore [OpenMAIC](#openmaic) for simulations, questions and presentation materials.

Each entry includes a first step and the practical requirements. The [Limitations](#limitations) section explains how to interpret the evidence and review generated material.

## Explore equations and physical systems

### marimo

**Type:** interactive scientific workbench with AI assistance

Connect equations, sliders, plots and simulations in a reactive Python notebook. Changing a parameter updates the calculations that depend on it. Readers can follow the code behind a picture and reuse the notebook as a script or app.

**Quick start:** browse the [project examples](https://github.com/marimo-team/marimo), choose a small numerical example and trace how its inputs affect the output. The [AI guide](https://docs.marimo.io/guides/generate_with_ai/) explains how to generate or refine cells and complete notebooks.

**Practical:** Apache-2.0. Python and a browser support ordinary notebook work. Hosted AI uses provider credentials and usage charges; [local-model configurations](https://docs.marimo.io/guides/configuration/llm_providers/) support Ollama and LM Studio. Release checked: [0.25.1, October 1, 2026](https://github.com/marimo-team/marimo/releases/tag/0.25.1).

### python-control

**Type:** computational library and worked teaching materials

Learn how mathematical models connect to feedback, trajectories and design choices. The [official examples](https://python-control.readthedocs.io/en/latest/examples.html) cover vehicle steering, aircraft model predictive control, VTOL linear-quadratic control, extended Kalman filtering, robust control and differential flatness.

**Quick start:** read one example's model assumptions, follow its code and compare its predicted response with the plots. The notebook examples provide a useful foundation for an interactive explanation in marimo or Jupyter.

**Practical:** [BSD-3-Clause](https://github.com/python-control/python-control/blob/main/LICENSE). Local Python computation uses NumPy, SciPy and Matplotlib; some routines also use Slycot. Core use has no LLM or paid API requirement. Source checked: [September 29, 2026](https://github.com/python-control/python-control/commit/b4cf7360138985f84afe299337ef9ee6c25e9c38).

### Ctrllib mechanics and passivity

**Type:** repository-local, machine-checked reading path for manipulator energy and coordinated passivity

Use this path to connect a generic manipulator equation to the coordinated-space identity in Giordano, Ott and Albu-Schäffer (2019). The paper's §II.C Eq. (4) is the generic `M v̇ + C v = u` starting point. The Ctrllib entry point is [`Ctrllib.manipulator_power_identity`](ctrllib/Ctrllib/ManipulatorEnergy.lean#L174-L190), which takes the richer instantaneous equation `M a + C v + g + D v = tau + Jᵀ f` and derives its velocity-power balance. [`Ctrllib.manipulatorEnergy_hasDerivAt`](ctrllib/Ctrllib/ManipulatorEnergy.lean#L192-L216) extends that calculation to a local storage derivative, while [`Ctrllib.manipulatorEnergy_deriv_le_power`](ctrllib/Ctrllib/ManipulatorEnergy.lean#L218-L243) adds the positive-semidefinite damping premise.

For the exact proof step that motivated the coordinated-control discussion, the paper's §III.B Eq. (23) is the printed quadratic cancellation used in the later stability argument. [`Ctrllib.transported_passivity_identity`](ctrllib/Ctrllib/PassivityTransport.lean#L85-L93) proves the transformed identity, and [`Ctrllib.circum_passivity_identity`](ctrllib/Ctrllib/CircumcentroidalPassivity.lean#L161-L177) is the concrete 9-dimensional reduced-block statement matching that equation. The paper does not call this a named “passivity theorem”; the release uses “passivity” for the matrix identity and labels the source step as part of the paper's stability proof. The release also retains [`Ctrllib.GiordanoErrata`](ctrllib/Ctrllib/GiordanoErrata.lean#L1-L15), whose small theorems witness two separately documented sign/block-order inconsistencies without claiming authorial intent.

**Primary source:** [Giordano, Ott and Albu-Schäffer, *Coordinated Control of Spacecraft's Attitude and End-Effector for Space Robots* (2019), DOI 10.1109/LRA.2019.2899433](https://doi.org/10.1109/LRA.2019.2899433), with an [author-hosted open record](https://elib.dlr.de/127691/) and [PDF](https://elib.dlr.de/127691/1/root.pdf).

**Scope:** the Ctrllib declarations are generic, finite-dimensional and local: they consume derivative and dynamics witnesses and do not establish a robot-specific zero-gravity model, ODE existence, parameters or controller implementation. The concrete passivity theorem is an exact formal counterpart of the paper's eq. 23 quadratic-form claim, under the stated inertia symmetry and transform construction; it is not a claim that every displayed equation in the paper is consistent. A quick source-first reading route is to open `ManipulatorEnergy.lean`, then `PassivityTransport.lean`, then `CircumcentroidalPassivity.lean`, and compare the theorem statements with the paper's eqs. 19–23.

### Penrose and Bloom

**Type:** mathematical diagram and interaction libraries

Describe mathematical relationships and visual constraints, then let Penrose arrange the diagram. Bloom adds interactive diagrams whose objects retain specified relationships as a reader drags them. Explore projections, geometry and coordinate constructions through direct manipulation.

**Quick start:** open the [interactive examples](https://penrose.cs.cmu.edu/docs/bloom/tutorial/interactivity), then follow the [Bloom tutorial](https://penrose.cs.cmu.edu/docs/bloom/tutorial/getting_started) to understand how a constraint connects the diagram to its mathematics.

**Practical:** [MIT-licensed project](https://github.com/penrose/penrose). Browser or JavaScript/TypeScript development; core functionality requires no LLM API or inference GPU. Release checked: [3.3.1, August 30, 2026](https://github.com/penrose/penrose/releases/tag/v3.3.1).

## Build and study visual explanations

### 3Blue1Brown video sources

**Type:** human-authored animation source collection

Study how an explanation introduces objects, changes viewpoint and connects a picture to a formula. The [video repository](https://github.com/3b1b/videos) contains the scene code behind 3Blue1Brown's mathematical videos, organized by year.

**Quick start:** choose a lesson from the [official website](https://www.3blue1brown.com/#lessons), watch its argument, then inspect the corresponding scene code. Follow the repository's workflow guide when adapting a scene.

**Practical:** the collection uses **CC BY-NC-SA 4.0**, including its noncommercial and share-alike conditions. The Manim engine has its own MIT license. Rendering uses ManimGL, LaTeX and compatible dependencies; reading the material requires no model or API. Source checked: [September 29, 2026](https://github.com/3b1b/videos/commit/306a1346a356c7a7b097875ceb51c5cd67d0a56c).

### Math-To-Manim

**Type:** AI-assisted mathematics and physics animation pipeline

Follow an idea through a learning brief, mathematical dossier, storyboard, generated scene and rendered film. The current [Math-To-Manim repository](https://github.com/HarleyCoops/Math-To-Manim) retains these intermediate artifacts and review records, giving readers material to inspect alongside the finished animation.

**Quick start:** explore a completed film and its linked source and production record. For generation, follow the current repository's setup and diagnostic instructions; use its saved-scene rendering route when revisiting existing work.

**Practical:** MIT. Python 3.10+, Node.js 18+, Manim dependencies, FFmpeg and LaTeX. The current primary generation route uses Codex login; optional TypeSafe Jev reviews use a separate credential. Model access and review usage determine costs. Release checked: [2.0.0, October 7, 2026](https://github.com/HarleyCoops/Math-To-Manim/releases/tag/v2.0.0).

### TheoremExplainAgent

**Type:** research implementation for narrated theorem videos

Explore how a system plans an explanation, generates Manim scenes, repairs execution errors and combines narration with animation. [TheoremExplainAgent](https://github.com/TIGER-AI-Lab/TheoremExplainAgent) includes generation code, evaluation code and a 240-topic benchmark spanning STEM subjects.

**Quick start:** watch the examples on the [project page](https://tiger-ai-lab.github.io/TheoremExplainAgent/), then inspect the README's single-topic generation path and the [paper's error analysis](https://arxiv.org/html/2502.19400).

**Practical:** MIT. Python 3.12, Manim, LaTeX/system dependencies, Kokoro speech weights and model-provider credentials. Hosted inference incurs usage charges; the paper's rendering setup required no GPU. Latest source commit checked: [July 27, 2025](https://github.com/TIGER-AI-Lab/TheoremExplainAgent/commit/e9ece5db7756b6ded8a812eceeb936cfd02aae21).

### Code2Video

**Type:** research implementation for educational video generation

See how a planner, coder and visual critic turn a learning topic into an executable visual explanation. [Code2Video](https://github.com/showlab/Code2Video) emphasizes storyboards, scene layout and refinement, and provides the 117-topic MMMC benchmark for studying generated lessons.

**Quick start:** compare the published examples, then follow the README's single-topic workflow. Read the [paper](https://arxiv.org/html/2510.01174) to understand its visual-quality and knowledge-transfer evaluations.

**Practical:** MIT for the code; external visual assets retain their own terms. Python/Manim plus LLM and vision-model credentials; optional asset services add requirements. Provider rates, selected models and retries determine cost. Latest source commit checked: [August 24, 2026](https://github.com/showlab/Code2Video/commit/1142d8e14cdc2806df85aedb0fbb5dca474caa0f).

## Create lessons and ask questions

### OpenMAIC

**Type:** AI lesson authoring and classroom application

Turn a topic or source document into a structured lesson with interactive HTML simulations, quizzes, whiteboards and voiced dialogue. [OpenMAIC](https://github.com/THU-MAIC/OpenMAIC) supports reusable exports, including editable presentations and classroom packages.

**Quick start:** review the examples and choose a small, clearly scoped topic. Follow the documentation for a stable release, then inspect the generated lesson's simulations and questions before sharing it.

**Practical:** root MIT license; the bundled mathml2omml component retains LGPL-3.0-or-later. Hosted models, speech and document parsing can incur separate charges. Local-provider options also exist. Stable release checked: [1.1.3, October 5, 2026](https://github.com/THU-MAIC/OpenMAIC/releases/tag/v1.1.3). The 1.2 release-candidate architecture adds PostgreSQL and a long-running server.

### AlgeBench

**Type:** experimental conversational 3D learning application

Ask questions while a narrator changes a mathematical or physical scene. [AlgeBench](https://github.com/ibenian/algebench) includes examples for eigenvalues, matrix transformations, Fourier series, gradient descent and orbital motion. Its agent tools expose sliders, numerical evaluation, camera movement and equation overlays.

**Quick start:** browse the [authored scenes](https://github.com/ibenian/algebench/tree/main/scenes) and [agent-tool reference](https://github.com/ibenian/algebench/blob/main/agent-tools-reference.md) to see which interactions each lesson supports.

**Practical:** MIT. Python/uv or Docker and a Gemini API key. The project describes a free-tier trial path; provider limits and speech usage can add costs. Source checked: [October 8, 2026](https://github.com/ibenian/algebench/commit/b76eab1bf718d319cfcf8c1b6a4d40c5e282419e).

### lean4-skills

**Type:** proof-linked learning workflow for coding agents

Investigate mathematical claims through questions, examples, counterexamples and source inspection. The [learning workflow](https://github.com/cameronfreer/lean4-skills/blob/main/plugins/lean4/commands/learn.md) supports Socratic sessions, exercises, informal explanations and Lean proof states. It records verification status for key claims and offers a strict verification mode.

**Quick start:** read the workflow, choose a small theorem or paper section and identify the corresponding Lean project or mathlib material. Consult the [installation guide](https://github.com/cameronfreer/lean4-skills/blob/main/INSTALLATION.md) for the available host integrations.

**Practical:** MIT. Requires Lean/mathlib and an AI coding-agent host; the project recommends lean-lsp-mcp. Host features and model charges vary. Version checked: [4.11.3, September 29, 2026](https://github.com/cameronfreer/lean4-skills/commit/b6243b85b9b0a0ddff5bb6773889044daf687f8e).

## Research and further reading

- **[LeanTutor](https://leantutor.org/) and [LeanSide](https://arxiv.org/html/2610.00760v1):** study how natural-language proof steps, feedback and Lean verification fit together. LeanSide includes a recent undergraduate linear-algebra deployment. Read as research and a project demonstration; a public software license and self-hosted release remain unverified.
- **[PedagogicalRL](https://github.com/eth-lre/PedagogicalRL) and [MathTutorBench](https://github.com/eth-lre/mathtutorbench):** investigate how to train and evaluate scaffolding, error diagnosis and question-driven tutoring. PedagogicalRL declares CC BY 4.0; [TutorRL-7B](https://huggingface.co/eth-nlped/TutorRL-7B) declares Apache-2.0. MathTutorBench's BY/BY-SA signals and component licenses need clarification before redistribution.
- **[MathDial](https://github.com/eth-nlped/mathdial):** read 2,861 human-teacher/simulated-student conversations to study teaching moves and responses to misconceptions. Its GitHub README states CC BY-SA 4.0; the [dataset card](https://huggingface.co/datasets/eth-nlped/mathdial) states CC BY 4.0. Retain the more restrictive conditions pending clarification.
- **[LLM2Manim](https://arxiv.org/html/2604.05266v1):** read a study of expert-reviewed animations with 100 undergraduates. It offers practical ideas about segmentation, notation consistency and human review. A public software release remains unverified.
- **[Generative Manim](https://github.com/marcelo-earth/generative-manim):** explore an Apache-2.0 code-generation, chat and rendering API when building a custom animation workflow. Its [API guide](https://github.com/marcelo-earth/generative-manim/blob/main/api/README.md) describes local/Docker setup and model-provider requirements.

## Limitations

### Mathematical fidelity

Check the original statement, assumptions, derivation and numerical behavior alongside each generated explanation. Successful rendering confirms that a program produced media. Formal checking confirms the encoded statement under its formal assumptions. Both require a separate check that the explanation and picture preserve the intended mathematics.

The distinction matters in measured systems: TheoremExplainAgent reports a correlation of only **0.14** between its automated accuracy/depth scores and human ratings. LeanSide reports that **18% of incorrect proof steps** in its study received unfaithful translations. These findings support source inspection and expert review. [TheoremExplainAgent paper](https://arxiv.org/html/2502.19400) · [LeanSide paper](https://arxiv.org/html/2610.00760v1)

### Learning evidence

Treat authoring features, benchmark performance, immediate quiz results and lasting learning as separate outcomes. Code2Video's human study involved 40 participants, mostly middle-school students. LLM2Manim studied two topics at one institution with expert-reviewed material and immediate assessments. PedagogicalRL reports synthetic-student results and explicitly leaves real-student validation open. The reviewed evidence does not establish reliable autonomous graduate-level tutoring. [Code2Video](https://arxiv.org/html/2510.01174) · [LLM2Manim](https://arxiv.org/html/2604.05266v1) · [PedagogicalRL](https://arxiv.org/html/2505.15607v2)

### Execution and data handling

This collection reviews public documentation and selected source files; it does not certify installation safety. Review dependencies and run generated code in an isolated environment with restricted filesystem and network access. A Python virtual environment manages dependencies; it does not provide a security boundary.

Local rendering and self-hosting can still send prompts, documents, notebook values, images or audio to configured providers. Review those destinations before supplying private material. OpenMAIC's document flow can begin uploading and parsing on attachment. AlgeBench describes its scene sandbox as best-effort and unaudited, particularly relevant to native JavaScript scenes. [OpenMAIC changelog](https://github.com/THU-MAIC/OpenMAIC/blob/main/CHANGELOG.md) · [AlgeBench sandbox model](https://github.com/ibenian/algebench/blob/main/docs/sandbox-model.md)

### Versions and reuse

Pin compatible versions when reproducing a lesson. ManimGL and Manim Community have different APIs; older scene code may need its original dependencies. Authored AlgeBench scenes can use capabilities beyond the live scene-builder's current coverage. Model-provider availability and pricing also change.

Review software, model, dataset and media licenses separately. The license facts above describe the checked sources and do not replace the actual terms. Keep required attribution and check permission before redistributing third-party assets or adapting noncommercial material.

## Keeping this collection useful

For additions and updates, include a primary project link, a concrete example, the relevant license, setup and cost requirements, and the date checked. Explain what a reader can learn or create. Label released software, reusable materials and research clearly, and attach evaluation claims to the study that supports them.

Recheck entries when upstream changes its license, generation workflow, provider requirements or supported versions. Preserve useful examples and replace stale instructions with links to the current official documentation.
