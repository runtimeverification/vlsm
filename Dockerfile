FROM ubuntu:focal

RUN    apt-get update               \
    && apt-get upgrade --yes        \
    && apt-get install --yes        \
                    build-essential \
                    curl            \
                    git             \
                    libgmp-dev      \
                    m4              \
                    rsync           \
                    unzip           \
                    wget

# Setup SSH/Git/GitHub

RUN    git config --global user.email 'admin@runtimeverification.com' \
    && git config --global user.name  'RV Jenkins'                    \
    && mkdir -p ~/.ssh                                                \
    && echo 'host github.com'                       > ~/.ssh/config   \
    && echo '    hostname github.com'              >> ~/.ssh/config   \
    && echo '    user git'                         >> ~/.ssh/config   \
    && echo '    identityagent SSH_AUTH_SOCK'      >> ~/.ssh/config   \
    && echo '    stricthostkeychecking accept-new' >> ~/.ssh/config   \
    && chmod go-rwx -R ~/.ssh
