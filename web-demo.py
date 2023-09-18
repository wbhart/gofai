
# this is a demo of the pythn package eel used to host a local webserver
# all html and js files relating to the web-interface are located in the web/ directory

# import the eel package for hosting the local webserver
import eel

# initialize eel
eel.init("web-demo")

# expose python function to the javascript code
@eel.expose	
def python_reverse_string(str):
	#call exposed javascript function
	eel.javascript_alert(str[::-1])

# start the local webserver at localhost
eel.start("demo.html")
