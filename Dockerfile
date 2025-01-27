# Copyright 2019 Shift Cryptosecurity AG
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Latest Ubuntu LTS
FROM ubuntu:18.04
ENV DEBIAN_FRONTEND noninteractive

RUN apt-get update && apt-get upgrade -y && apt-get install -y wget nano rsync curl gnupg2 jq

# for clang-*-8, see https://apt.llvm.org/
RUN echo "deb http://apt.llvm.org/bionic/ llvm-toolchain-bionic-8 main" >> /etc/apt/sources.list && \
    echo "deb-src http://apt.llvm.org/bionic/ llvm-toolchain-bionic-8 main" >> /etc/apt/sources.list && \
    wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add -

# Install gcc8-arm-none-eabi
RUN mkdir ~/Downloads &&\
    cd ~/Downloads &&\
    wget -O gcc.tar.bz2 https://developer.arm.com/-/media/Files/downloads/gnu-rm/8-2018q4/gcc-arm-none-eabi-8-2018-q4-major-linux.tar.bz2?revision=d830f9dd-cd4f-406d-8672-cca9210dd220?product=GNU%20Arm%20Embedded%20Toolchain,64-bit,,Linux,8-2018-q4-major &&\
    echo "fb31fbdfe08406ece43eef5df623c0b2deb8b53e405e2c878300f7a1f303ee52 gcc.tar.bz2" | sha256sum -c &&\
    cd ~/Downloads &&\
    tar -xjvf gcc.tar.bz2 &&\
    rm -f gcc.tar.bz2 &&\
    cd ~/Downloads && rsync -a gcc-arm-none-eabi-8-2018-q4-major/ /usr/local/

# Install nanopb
RUN cd ~/Downloads &&\
    wget https://jpa.kapsi.fi/nanopb/download/nanopb-0.3.9.2-linux-x86.tar.gz &&\
    echo "00624f2834066ab31613dd2bb53b258a3b81cd83554df4a7cf49725c5cf34c46 nanopb-0.3.9.2-linux-x86.tar.gz" | sha256sum -c &&\
    tar -xvzf nanopb-0.3.9.2-linux-x86.tar.gz &&\
    rm -f nanopb-0.3.9.2-linux-x86.tar.gz &&\
    mv ~/Downloads/nanopb-0.3.9.2-linux-x86/generator-bin/protoc* /usr/local/bin/ &&\
    mv ~/Downloads/nanopb-0.3.9.2-linux-x86/generator-bin/nanopb_generator /usr/local/bin/ &&\
    mv ~/Downloads/nanopb-0.3.9.2-linux-x86/generator-bin/libpython*so* /usr/local/bin/ &&\
    mv ~/Downloads/nanopb-0.3.9.2-linux-x86/generator-bin/*so* /usr/local/lib/ &&\
    mv ~/Downloads/nanopb-0.3.9.2-linux-x86/generator-bin/include/* /usr/local/include/ &&\
    mv ~/Downloads/nanopb-0.3.9.2-linux-x86/generator/proto/google/ /usr/local/include/

# Tools for building
RUN apt-get update && apt-get install -y \
    build-essential \
    gcc-8 \
    binutils \
    valgrind \
    cmake \
    git \
    autotools-dev \
    automake \
    autoconf \
    libtool \
    pkg-config \
    libcmocka-dev \
    libc6-i386 \
    lib32stdc++6 \
    lib32z1 \
    libusb-1.0-0-dev \
    libudev-dev

# Set gcc-8 as the default gcc
RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 100
RUN update-alternatives --install /usr/bin/gcov gcov /usr/bin/gcov-8 100

# Tools for CI
RUN apt-get update && apt-get install -y \
    python3 \
    python3-pip \
    clang-format-8 \
    clang-tidy-8

# Python modules
RUN pip3 install \
    hidapi \
    noiseprotocol \
    protobuf \
    ecdsa \
    tzlocal \
    semver

# Python modules for CI
RUN pip3 install \
    pylint \
    pylint-protobuf \
    black

# Install Go, used for the tools in tools/go and for test/gounittest
ENV GOPATH /opt/go
ENV GOROOT /opt/go_dist/go
ENV PATH $GOROOT/bin:$GOPATH/bin:$PATH
RUN mkdir -p /opt/go_dist && \
    curl https://dl.google.com/go/go1.11.linux-amd64.tar.gz | tar -xz -C /opt/go_dist

# Install lcov from release (the one from the repos is too old).
RUN cd /opt && wget https://github.com/linux-test-project/lcov/releases/download/v1.14/lcov-1.14.tar.gz && tar -xf lcov-1.14.tar.gz
ENV PATH /opt/lcov-1.14/bin:$PATH

# Clean temporary files to reduce image size
RUN rm -rf /var/lib/apt/lists/*
