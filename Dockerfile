FROM ubuntu:latest
RUN apt-get update && apt-get install -y default-jre
COPY . /app
WORKDIR /app
CMD ["java", "-cp", "lib/tla2tools.jar", "tlc2.TLC", "TrafficLight.tla"]
