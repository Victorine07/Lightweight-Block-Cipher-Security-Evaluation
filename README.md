
# Lightweight Block Cipher Security Evaluation using Formal Methods and Graph Neural Networks

Formal Verification-Driven ML Framework for Security Evaluation of Lightweight Block Ciphers


This repository contains the code and methodology for evaluating the security of lightweight block ciphers. 
The project implements a novel framework based on ciphers' formal cipher specifications from Isabelle/HOL, to extract Abstract Syntax Trees (ASTs) and metadata, to train a hybrid Graph Neural Network (GNN) and Multi-Layer Perceptron (MLP) model to analyze the ciphers' security properties.

The ciphers analyzed in this work include:
* PRESENT
* Simon
* Speck
* HIGHT



## Project Workflow

The project is structured as a four-step pipeline, with each step implemented in a Jupyter Notebook.

### 1. Variant Generation
* **Notebook:** `STEP-1-thy variants generation.ipynb`
* **Purpose:** For each cipher, this file is used to generate the theory files for the ciphers' variants. It uses the theory file templates for each cipher and generates the standard variants given their specific key size, block size, number of rounds, and other parameters.


### 2. AST and PDV Extraction
* **Notebook:** `STEP-2-thy2AST_json generation-V2.ipynb`
* **Purpose:** The generated Isabelle/HOL theory files are parsed and Abstract Syntax Trees (ASTs) and Protocol Design Vector (PDV) are extracted.
* For each cipher, the code extracts nodes and edges with essential information from core cryptographic functions to form the corresponding AST
* The PDV is used to extract ciphers' metadata
* These tree structures and PDV  are then saved in JSON format, making them readable for machine learning processing.


### 3. Data Augmentation and Sampling
* **Notebook:** `STEP-3-Augmentation Strategies-V2.ipynb`
* **Purpose:** This step applies data augmentation techniques on the textual and structural levels to the generated JSON files and samples the different files.
* This is done to generate datasets of different sizes to perform sensitivity analysis.
 

### 4. Hybrid Model Training
* **Notebook:** `STEP-4-Training Hybrid Model-GNN-MLP-V2.ipynb`
* **Purpose:** Training a hybrid model, combining a Graph Neural Network (GNN) to understand the code's structure (the AST) and a Multi-Layer Perceptron (MLP) to understand the MLP on the generated datasets. 
* **Goal:** The model is trained to learn and assess the security level of Simon, Speck and PRESENT, and is tested on an unknown cipher, HIGHT.



##  Repository Structure

* **`*.ipynb`**: The four Jupyter Notebooks that form the main experimental pipeline.
* **`*.thy`**: Isabelle/HOL theory files.
    * `*_template.thy`: Base templates for ciphers: PRESENT, Simon, and Speck.
    * `HIGHT_64_128.thy`: Formal Specification for HIGHT cipher.
* **`cipher_profiles.py`**: Contains the cryptographical and security details on the cipher profiles for Simon, Speck, PRESENT and HIGHT cipher.
* **`samples_per_variant_k`**: generated dataset after augmentation and sampling for dataset-k, f ranging from 1 to 10.




##  Installation & Dependencies

This project is run using Python 3.8 and the following libraries:

* Core Libraries: json, os, re, random, subprocess
* Data Science & ML: numpy, pandas, scikit-learn 
* Deep Learning (GNN & MLP): torch, torch_geometric 




## Disclaimer

**This project utilized Large Language Models (LLMs) in its development.** LLMs were used to: 
1.  Assist in creating the formal theory files (`.thy`) for the ciphers from their original Python implementations.
2.  Assist in developing the data augmentation strategies applied to the JSON (AST) files.
3.  Assisting with the model training and tuning process.


