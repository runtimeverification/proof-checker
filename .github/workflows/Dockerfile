FROM ubuntu:jammy

ARG PYTHON_VERSION=3.10

RUN    apt-get -y update                \
    && apt-get -y install               \
         curl                           \
         graphviz                       \
         python${PYTHON_VERSION}        \
         python${PYTHON_VERSION}-venv   \
         python${PYTHON_VERSION}-dev    \
    && apt-get -y clean

ARG USER_ID=9876
ARG GROUP_ID=9876
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user/
ENV PATH=/home/user/.cargo/bin:/home/user/.local/bin:${PATH}

RUN    curl -sSL https://install.python-poetry.org | POETRY_HOME=/usr python${PYTHON_VERSION} - \
    && poetry --version
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -- /dev/stdin -y
RUN rustup default nightly
