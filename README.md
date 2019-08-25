# I4
I4 is an automated inductive invariant generator for distributed protocols.

## Dependency
[Ivy](http://microsoft.github.io/ivy/install.html), [Averroes](https://github.com/aman-goel/avr/tree/distributed)(distributed branch).

Run script `bash dependencies.sh` to automatically install Ivy and Averroes.

## How to run
1. Start with a protocol, run `translate.py` in python2 to generate a finite instance in vmt format. Specify each sort's amount for the desired model size.  
    ```
    python translate.py lock_server/lock_server.ivy client=2 server=1 > tmp.vmt
    ```
    This will produce a finite instance that is just enough to generate inductive invariants for the generate case for `lock_server.ivy`.

2. Use [Averroes](https://github.com/aman-goel/avr/tree/distributed)  to generate invariants for the finite instance.
    ```
    cd avr
    python avr.py --vmt ../tmp.vmt -e 4
    ```
   * When [Averroes](https://github.com/aman-goel/avr/tree/distributed) finds a counter example, the finite instance is buggy and it requires a manual fix to the protocol.
   * Otherwise, `output/work_test/inv.txt` for the finite instance is generated.
   * Some detailed information can be found in `output/work_test/test.result`. `scalls` shows the total number of SMT calls; `time-dist-inv-induct-check` shows the percentage of total time spent in minimizing the inductive invariant; `time` shows the total time for finding and minimizing the inductive invariant.
  
3. Remove redundant information in `inv.txt`.
    ```
    python remove.py avr/output/work_lock_server/inv.txt > inv.txt
    ```

4. Compile `main.cpp`.
    ```
    g++ main.cpp -o main -std=c++11
    ```
    `main` verifies whether the generated invariant is the inductive invariant of the (possibly infinite) protocol.  
    `main` requires following as input: the protocol `$MODEL_NAME$.ivy`,  an invariant file (inv.txt) that is generated in the previous step, and an associated config file.

    ### config file
    * config file is usually named after `config_$MODEL_NAME$.txt`.
    * A config file has 3 parts. Each part starts with an integer that specifies the number of variables/constants each part defines, followed by a newline. 
    * Each definition takes a newline.
    * The first part lists all the relations and functions (variables).  
    Format: number of inputs, type of return value, name of relation/function \[, type of input1\][, type of input2, ...], Each separated by a space.  
    E.g.
        ```
        2 boolean le TYPE1 TYPE1
        1 TYPE1 some_relation TYPE2
        ```
    * The second part lists all individuals that are named after zero, first, org, if showing up in `$MODEL_NAME$.ivy`.
    Format: type of individual, name of an individual in **uppercase**, `=`, the number '0'. Each separated by a space.  
    E.g.
        ```
        TYPE1 first = 0
        TYPE1 org = 0
        ```
      If one wishes to assign different values or to use more variable names, modify the 
    * The third part is not used now, thus it contains only the number 0.

    Now we can run main: `./main model_file invariant_file config_file [invariant_prefix]`. For example:
    ```
    ./main lock_server/lock_server inv.txt lock_server/config_lock_server.txt
    ```
    and the output is `$model_file$_inv.ivy`. It may or may not pass `ivy_check $MODEL_NAME$_inv.ivy`; if it does not, go back to step 1 and increase the model size.

    Check `log.txt` for more information.

5. `bash test.sh` runs all models and generates all `$model_file$_inv.ivy`.