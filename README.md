# rpi-srv
Monitoring server for my RPi and attached UPS.

The code is used for monitor my UPS for Raspberry Pi (RPi) and some parameters of the RPi. An ADC chip is integrated on the UPS which can measure voltage levels at various points on PCB. The chip is Microchip MCP3008: http://www.microchip.com/wwwproducts/en/MCP3008. Besides voltage levels the server can monitor also some parameters of the RPi itself. For now it is intended to measure die temperature.

As a consequence the code is unusable without the UPS PCB itself. I created the repository for two main tasks:
1) to learn how to work with git and github;
2) to simplify my workflow given that usually I work from separate hosts.

Perhaps I'll add PCB design of the UPS later if I'll having a chance to find enough free time.
