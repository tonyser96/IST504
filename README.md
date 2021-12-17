# IST504
For Lab 3 Submission

The actual submission files are the ones outside of the two folders. Those inside the folders are only included as additional reference.

***Note - for some reason, the regular command to run my verify script (make verify INPUT=*) doesn't work for me on my VM. Instead, I had to modify the verify script a little and run it with "python verify ./class-input/*", which was what I did during my live demo**
However, these scripts should be able to be made and verified normally on other systems without any required modifications.

Working (CORRECT):
- All inputs within the medium and long folder.
- All inputs within the inst folder (* For some reason, the verify script results in errors with some inputs. However, when the .sim and .refsim files are run individually, their outputs are actually the same. There appears to be issues with the verify script itself.)

Working, but with issues (Partially Incorrect):
- Inputs 1-6 from the random folder. The cycles are slightly off from the correct simulation, but everything else were simulated correctly.

Credits due to their respective original authors (see each file for more info).
