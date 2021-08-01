Repo for collected work on Attacker Classification project with Cole, Stavros, and Eunsuk.

# Running
- install Java 11
- `./build.sh` + one of {"sym", "pub", ""}
- use `>` to dump log to a file
  - ex. `./build.sh sym > out.txt`
## Stats
Allows you to see the running times of each command, assuming you've written the run to a file `out.txt`:
- `pip install prettytable`
- `python3 print_timings.py out.txt`

# Alloy Changes Instructions
- change Alloy files directly in local copy
- run `./gradlew build`
- run `./singleAlloyBuild.sh` in local Alloy copy
- copy resulting jar file to `alloy/`
- make java path look to that jar by changing path in `.vscode/settings.json`

# Questions
- You could imagine a violation that only occurs in a model when the time bound is increased to 10.
  - should we just say, our technique only guarantees attack space coverage up to the bound set by the user?
  - is this type of caveat typical of bounded approaches?