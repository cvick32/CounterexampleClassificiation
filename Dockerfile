FROM openjdk:11
COPY . /usr/AttackClassification
WORKDIR /usr/AttackClassification
RUN sh -c "$(wget -O- https://github.com/deluan/zsh-in-docker/releases/download/v1.1.2/zsh-in-docker.sh)"



