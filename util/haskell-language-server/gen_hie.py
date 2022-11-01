import os
import yaml

file_dir = os.path.dirname(__file__)
os.chdir(f"{file_dir}/../../src/comp")

# all the directories that might contain haskell
# sources
dirs = [
    ".",
    "./Libs",
    "./GHC",
    "./GHC/posix",
    "./Parser",
    "./Parser/BSV",
    "./Parser/Classic",
    "../Parsec",
    "../vendor/stp/include_hs",
    "../vendor/yices/include_hs",
    "../vendor/htcl"
]

arguments = ["-i"]
arguments += [f"-i{dir}" for dir in dirs]

# collect haskell sources
hs_srcs = []
for dir in dirs:
    hs_srcs += [f"{dir}/{f}" for f in os.listdir(dir) if f[-3:] == ".hs"]

# collect literate haskell sources
lhs_srcs = []
for dir in dirs:
    lhs_srcs += [f"{dir}/{f}" for f in os.listdir(dir) if f[-4:] == ".lhs"]

# form arguments
arguments += hs_srcs + lhs_srcs

# form and dump yaml file
hie_yaml = {"cradle":{"direct":{"arguments":arguments}}}
f = open("hie.yaml", "w")
f.write(yaml.dump(hie_yaml))