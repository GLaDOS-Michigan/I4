# export PYTHONPATH=ivy/ivy/:$PYTHONPATH
export LD_LIBRARY_PATH=/usr/local/lib:
export PYTHONPATH=/usr/local/lib/python2.7/site-packages:$PYTHONPATH

cp translate.py ivy/ivy

echo 'lock server'
pushd .
cd ivy/ivy
python translate.py ../../lock_server/lock_server.ivy client=2 server=1 > ../../tmp.vmt
popd
pushd .
cd avr
python avr.py --vmt ../tmp.vmt -e 4
popd
python remove.py avr/output/work_test/inv.txt > inv.txt
time ./main lock_server/lock_server inv.txt lock_server/config_lock_server.txt
echo 'lock server done!'
echo ''

echo 'leader election'
pushd .
cd ivy/ivy
python translate.py ../../leader/leader.ivy node=3 id=3 > ../../tmp.vmt
popd
pushd .
cd avr
python avr.py --vmt ../tmp.vmt -e 4
popd
python remove.py avr/output/work_test/inv.txt > inv.txt
time ./main leader/leader inv.txt leader/config_leader.txt "idn(N0) = ID0 & idn(N1) = ID1 & idn(N2) = ID2 & "
echo 'leader election done!'
echo ''

echo 'distributed lock'
pushd .
cd ivy/ivy
python translate.py ../../distributed_lock/distributed_lock.ivy node=2 epoch=4 > ../../tmp.vmt
popd
pushd .
cd avr
python avr.py --vmt ../tmp.vmt -e 4
popd
python remove.py avr/output/work_test/inv.txt > inv.txt
time ./main distributed_lock/distributed_lock inv.txt distributed_lock/config_distributed_lock.txt
echo 'distributed lock done!'
echo ''

echo 'chord ring'
pushd .
cd ivy/ivy
python translate.py ../../chord/chord.ivy node=4 > ../../tmp.vmt
popd
pushd .
cd avr
python avr.py --vmt ../tmp.vmt -e 4
popd
python remove.py avr/output/work_test/inv.txt > inv.txt
time ./main chord/chord inv.txt chord/config_chord.txt
echo 'chord ring done!'
echo ''

echo 'learning switch'
pushd .
cd ivy/ivy
python translate.py ../../switch/switch.ivy node=3 packet=1 > ../../tmp.vmt
popd
pushd .
cd avr
python avr.py --vmt ../tmp.vmt -e 4
popd
python remove.py avr/output/work_test/inv.txt > inv.txt
time ./main switch/switch inv.txt switch/config_switch.txt
echo 'learning switch done!'
echo ''

echo 'database chain replication'
pushd .
cd ivy/ivy
python translate.py ../../chain/chain.ivy transaction=3 operation=3 key=1 node=2 > ../../tmp.vmt
popd
pushd .
cd avr
python avr.py --vmt ../tmp.vmt -e 4
popd
python remove.py avr/output/work_test/inv.txt > inv.txt
time ./main chain/chain inv.txt chain/config_chain.txt
echo 'database chain replication done!'
echo ''

echo 'two phase commit'
pushd .
cd ivy/ivy
python translate.py ../../2PC/2PC.ivy node=6 > ../../tmp.vmt
popd
pushd .
cd avr
python avr.py --vmt ../tmp.vmt -e 4
popd
python remove.py avr/output/work_test/inv.txt > inv.txt
time ./main 2PC/2PC inv.txt 2PC/config_2PC.txt
echo 'two phase commit done!'
echo ''
