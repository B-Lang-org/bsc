FROM ubuntu:18.04 as build
ADD .github/workflows/install_dependencies_ubuntu.sh /build/
RUN DEBIAN_FRONTEND=noninteractive \
    /build/install_dependencies_ubuntu.sh
ADD . /build/
RUN make -C /build -j2 GHCJOBS=2 GHCRTSFLAGS='+RTS -M5G -A128m -RTS'
RUN make -C /build check

FROM ubuntu:18.04
RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive \
       apt-get install -y \
          build-essential iverilog \
          $(apt-cache search -n '^(tk-)?itk[0-9]-dev' | cut -f1 -d' ' | sort | tail -1) \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /build/inst /opt/bluespec/
ENV PATH /opt/bluespec/bin:$PATH
