# Installing
- clone this repository
- install docker
  - for Ubuntu run
    - `sudo apt update`
    - `sudo apt install docker.io`

# Running
- `cd CounterexampleClassification`
- run `docker build -t counterexample-classification .`
- run `docker run -it counterexample-classification sh`
  - `it` flag lets us run interactively and executes `sh` on the
    container, so we have a terminal
- now we're in the container and we can run the `build.sh` script like so:
  - `./build.sh tcp all 7 T`
    - first arg is the experiment: `{sym, pub, tcp, pc}`
    - second arg is predicate set: `{all, default}`
    - third arg is scope: `{1~25}`
      - can go higher, but the program will likely run out of memory
    - fourth arg is redundancy check: `{T, F}`
      - checks whether we want to check for redundant classes or not
        at the end of classification

