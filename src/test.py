import os

if __name__ == "__main__":
    fList = os.listdir("./traces")
    for fName in fList:
        if(fName[-3:] == "rep"):
            inputDir = "".join(["./traces/", fName])
            outputDir = "".join(["./result_ILA/", fName])
            os.system("./mdriver -V -f " + inputDir + " > " + outputDir)