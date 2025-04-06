# Use Ubuntu 22.04 as the base image
FROM ubuntu:22.04 as builder

# Set environment variables for GHC and Cabal versions
ARG GHC_VERSION=8.10.7
ARG CABAL_VERSION=3.12.1.0
ARG HLS_VERSION=1.10.0.0

# Prevent timezone configuration prompts
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# Create necessary directories
RUN echo "Creating directories..." && \
    mkdir -p /opt/ghc /opt/cabal/bin /opt/ccache

# Install system dependencies and LLVM
RUN echo "Installing system dependencies and LLVM..." && \
    apt-get update && \
    apt-get install -y --no-install-recommends \
        curl \
        wget \
        build-essential \
        libffi-dev \
        libgmp-dev \
        libtinfo-dev \
        libncurses-dev \
        libnuma-dev \
        libtinfo5 \
        libncurses5 \
        libgmp10 \
        libffi7 \
        libnuma1 \
        zlib1g-dev \
        git \
        python3 \
        python3-pip \
        python3-dev \
        libpython3.10-dev \
        libxml2-dev \
        libicu-dev \
        liblzma-dev \
        libz3-dev \
        libssl-dev \
        pkg-config \
        llvm-12 \
        llvm-12-dev \
        clang-12 \
        libclang-12-dev \
        libclang-cpp12-dev \
        python3-clang-12 \
        autoconf \
        gperf \
        flex \
        bison \
        tcl \
        tcl-dev \
        && rm -rf /var/lib/apt/lists/* && \
    update-alternatives --install /usr/bin/opt opt /usr/bin/opt-12 100 && \
    update-alternatives --install /usr/bin/llc llc /usr/bin/llc-12 100

# Set LLVM environment variables
ENV PATH="/usr/lib/llvm-12/bin:${PATH}"
ENV LLVM_CONFIG=/usr/bin/llvm-config-12

# Install GHCup
RUN echo "Installing GHCup..." && \
    curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 sh

# Install GHC and Cabal
RUN echo "Installing GHC and Cabal..." && \
    . "$HOME/.ghcup/env" && \
    ghcup install ghc ${GHC_VERSION} && \
    ghcup install cabal ${CABAL_VERSION} && \
    ghcup set ghc ${GHC_VERSION} && \
    ghcup set cabal ${CABAL_VERSION}

# Update Haskell dependencies
RUN echo "Updating Haskell dependencies..." && \
    . "$HOME/.ghcup/env" && \
    cabal update && \
    cabal install --lib \
        aeson \
        base \
        bytestring \
        containers \
        directory \
        filepath \
        mtl \
        process \
        text \
        time-1.9.3 \
        transformers \
        unix \
        vector \
        yaml \
        regex-compat \
        syb \
        old-time \
        split

# Set up CCache
RUN echo "Setting up CCache..." && \
    apt-get update && \
    apt-get install -y ccache && \
    mkdir -p /root/.ccache && \
    echo "max_size = 5.0G" > /root/.ccache/ccache.conf && \
    rm -rf /var/lib/apt/lists/*

# Install Haskell Language Server if version is specified
RUN if [ -n "${HLS_VERSION}" ]; then \
        echo "Installing Haskell Language Server..." && \
        . "$HOME/.ghcup/env" && \
        ghcup install hls ${HLS_VERSION} && \
        ghcup set hls ${HLS_VERSION} && \
        echo "Testing Haskell Language Server..." && \
        echo "HLS bin directory contents:" && \
        ls -la $HOME/.ghcup/hls/${HLS_VERSION}/bin && \
        echo "PATH:" && \
        echo $PATH && \
        export PATH="$HOME/.ghcup/hls/${HLS_VERSION}/bin:$PATH" && \
        haskell-language-server-wrapper --version; \
    fi

# Build BSC
WORKDIR /app
COPY . .
RUN echo "Installing regex-compat and dependencies..." && \
    . "$HOME/.ghcup/env" && \
    echo "Current GHC version:" && \
    ghc --version && \
    echo "Installing regex-compat and dependencies..." && \
    cabal install --global --lib --force-reinstalls \
        regex-base-0.94.0.2 \
        regex-posix-0.96.0.1 \
        regex-compat-0.95.2.1 && \
    echo "Installing other required packages..." && \
    cabal install --global --lib --force-reinstalls \
        syb \
        old-time \
        split && \
    echo "Registering packages with ghc-pkg..." && \
    find /root/.cabal/store/ghc-8.10.7 -name '*.conf' -exec ghc-pkg register {} \; && \
    echo "Checking installed packages:" && \
    ghc-pkg list

RUN echo "Building BSC..." && \
    . "$HOME/.ghcup/env" && \
    pwd && \
    ls -la && \
    cd src && \
    pwd && \
    ls -la && \
    if [ -f Makefile ]; then \
        echo "Makefile exists:" && \
        cat Makefile && \
        sh -x -c ". $HOME/.ghcup/env && make install" 2>&1; \
    else \
        echo "Makefile not found!"; \
    fi

# Test GHCI integration
RUN echo "Testing GHCI integration..." && \
    . "$HOME/.ghcup/env" && \
    ghci -e "putStrLn \"Hello, World!\""

# Runtime stage
FROM ubuntu:22.04

# Prevent timezone configuration prompts
ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# Copy GHC, Cabal, and BSC installation from builder
COPY --from=builder /opt/ghc /opt/ghc
COPY --from=builder /opt/cabal /opt/cabal
COPY --from=builder /usr/local/bin /usr/local/bin
COPY --from=builder /usr/local/lib /usr/local/lib

# Install runtime dependencies
RUN echo "Installing runtime dependencies..." && \
    apt-get update && \
    apt-get install -y --no-install-recommends \
        libgmp10 \
        libffi7 \
        libtinfo5 \
        libncurses5 \
        libnuma1 \
        zlib1g \
        python3 \
        python3-pip \
        libpython3.10 \
        libxml2 \
        libicu70 \
        liblzma5 \
        libz3-4 \
        libssl3 \
        && rm -rf /var/lib/apt/lists/*

# Set up environment
ENV PATH="/opt/ghc/bin:/opt/cabal/bin:$PATH"

# Set working directory
WORKDIR /app

# Default command
CMD ["bsc"]
