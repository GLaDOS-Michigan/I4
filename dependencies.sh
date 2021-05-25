apt-get update
apt-get install python
apt-get install python-pip
apt-get install g++

echo "Building Z3"
wget https://github.com/Z3Prover/z3/archive/z3-4.6.0.tar.gz
tar xzf z3-4.6.0.tar.gz
pushd .
cd z3-z3-4.6.0/
python scripts/mk_make.py --prefix=/usr/local --python --pypkgdir=/usr/local/lib/python2.7/site-packages
cd build
make -j 4
sudo make install
export LD_LIBRARY_PATH=/usr/local/lib:
export PYTHONPATH=/usr/local/lib/python2.7/site-packages:$PYTHONPATH
popd

echo "Building Ivy"
sudo apt-get install python-ply python-pygraphviz
sudo pip install ply pygraphviz tarjan
sudo apt-get install python-tk tix
git clone https://github.com/GLaDOS-Michigan/ivy.git
pushd .
cd ivy
sudo python setup.py install
popd

echo "Building AVR"
git clone https://github.com/GLaDOS-Michigan/avr.git
pushd .
cd avr
git checkout distributed
sudo apt-get install clang
sudo apt-get install tcl8.6-dev
sudo apt-get install libreadline-dev
sudo apt-get install flex bison
bash build.sh
popd
