/*
 *  Copyright (c), 2009 Carnegie Mellon University.
 *  All rights reserved.
 *  
 *  Use in source and binary forms, with or without modifications, are permitted
 *  provided that that following conditions are met:
 *  
 *  1. Source code must retain the above copyright notice, this list of
 *  conditions and the following disclaimer.
 *  
 *  2. Binary form must reproduce the above copyright notice, this list of
 *  conditions and the following disclaimer in the documentation and/or
 *  other materials provided with the distribution.
 *  
 *  Permission to redistribute source and binary forms, with or without
 *  modifications, for any purpose must be obtained from the authors.
 *  Contact Rohit Kumar (rohitk@cs.cmu.edu) for such permission.
 *  
 *  THIS SOFTWARE IS PROVIDED BY CARNEGIE MELLON UNIVERSITY ``AS IS'' AND
 *  ANY EXPRESSED OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 *  THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 *  PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL CARNEGIE MELLON UNIVERSITY
 *  NOR ITS EMPLOYEES BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *  
 */
package basilica2.tutor.listeners;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.xerces.parsers.DOMParser;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import basilica2.agents.components.InputCoordinator;
import basilica2.agents.events.MessageEvent;
import basilica2.agents.events.PresenceEvent;
import basilica2.agents.events.PromptEvent;
import basilica2.agents.events.priority.PriorityEvent;
import basilica2.agents.events.priority.BlacklistSource;
import basilica2.agents.events.priority.PriorityEvent.Callback;
import basilica2.agents.listeners.BasilicaAdapter;
//import basilica2.social.data.TurnCounts;
import basilica2.tutor.events.DoTutoringEvent;
import basilica2.tutor.events.DoneTutoringEvent;
import basilica2.tutor.events.MoveOnEvent;
import basilica2.tutor.events.StudentTurnsEvent;
import basilica2.tutor.events.TutorTurnsEvent;
import basilica2.tutor.events.TutoringStartedEvent;
import edu.cmu.cs.lti.basilica2.core.Agent;
import edu.cmu.cs.lti.basilica2.core.Event;
import edu.cmu.cs.lti.project911.utils.log.Logger;
import edu.cmu.cs.lti.project911.utils.time.TimeoutReceiver;
import edu.cmu.cs.lti.project911.utils.time.Timer;
import edu.cmu.cs.lti.tutalk.script.Concept;
import edu.cmu.cs.lti.tutalk.script.Response;
import edu.cmu.cs.lti.tutalk.script.Scenario;
import edu.cmu.cs.lti.tutalk.slim.EvaluatedConcept;
import edu.cmu.cs.lti.tutalk.slim.FuzzyTurnEvaluator;
import edu.cmu.cs.lti.tutalk.slim.TuTalkAutomata;

/**
 * 
 * @author rohitk --> dadamson --> gtomar
 */
public class TutorActor extends BasilicaAdapter implements TimeoutReceiver
{


	private boolean isTutoring = false;
	private boolean expectingResponse = false;
	private boolean nullExpected = false;
	private TuTalkAutomata currentAutomata = null;
	private String currentConcept = null;
	private List<String> lastTutorTurns = null;
	private int noMatchingResponseCount = 0;
	private List<String> answerers = null;
	private Map<String, Dialog> pendingDialogs = new HashMap<String, Dialog>();
	private Map<String, Dialog> proposedDialogs = new HashMap<String, Dialog>();
	private String enlistedDialog = null;
	private InputCoordinator source;
	
	private double tutorMessagePriority = 0.75;
	private boolean interruptForNewDialogues = false;
	private boolean startAnyways = true;
	private String dialogueFolder = "dialogs";
	
	private String dialogueConfigFile = "dialogues/dialogues-example.xml";
	private int introduction_cue_timeout = 60;
	private int introduction_cue_timeout2 = 60;
	private int tutorTimeout = 45;
	private String request_poke_prompt_text = "I am waiting for your response to start. Please ask for help if you are stuck.";
	private String goahead_prompt_text = "Let's go ahead with this.";
	private String response_poke_prompt_text = "Can you rephrase your response?";
	private String dont_know_prompt_text = "Anybody?";
	private String moving_on_text = "Okay, let's move on.";
	private String tutorialCondition = "tutorial";
	private int numUser = 1;
	
	private boolean block = false;

	// private List<Dialog> dialogsReadyQueue = new ArrayList<Dialog>();

	class Dialog
	{

		public String conceptName;
		public String scenarioName;
		public String introText;
		public String acceptAnnotation;
		public String acceptText;
		public String cancelAnnotation;
		public String cancelText;

		public Dialog(String conceptName, String scenarioName, String introText, String cueAnnotation, String cueText, String cancelAnnotation, String cancelText)
		{
			this.conceptName = conceptName;
			this.scenarioName = scenarioName;
			this.introText = introText;
			this.acceptAnnotation = cueAnnotation;
			this.acceptText = cueText;
			this.cancelAnnotation = cancelAnnotation;
			this.cancelText = cancelText;

			/* Behzad 
			 * It is about adding random elements in whatever the agent wants to say. In this version, a phrase is selected randomly when a Dialog object wants to be created.
			 * If you want to add random elements in a specific scenario, follow these steps:
			 * 1. create this folder: runtime/data
			 * 2. create this folder: runtime/data/<conceptName of scenario> 
			 * 3. create this file: runtime/data/<conceptName of scenario>/<use a string that you want to replace it with random elements>.txt 
			 *     3.1 the name of txt file should be lower case and the name in scenario file should be upper case
			 *     3.2 each row of this txt file contains a phrase
			 *     
			 *      
			 * For example: 
			 * 	This is my random file: runtime/data/IDSAI/random_example.txt in which each line has a phrase 
			 *     a fish
			 *     a baby
			 *     a table
			 *     ...
			 *     
			 *  and in the scenario file scenario-idsai.xml, in concepts tag, we have:
			 *  <concept label="question1">
			 *		<phrase>Is RANDOM_EXAMPLE intelligent or not? Why? </phrase>
			 *	</concept>
			 *
			 * When the Dialog object is creating, RANDOM_EXAMPLE will be replaced with the one of the elements in random_example.txt
			 * 
			 * 
			 * We can use this method to add HTML tags in responses.
			 * 
			 * PLEASE LOOK AT THE "IDSAIAgent\runtime\dialogues\scenario-idsai.xml" AND THE FILES OF THIS FOLDER "\IDSAIAgent\runtime\data\IDSAI"
			 */ 
			File folder = new File("data/" + conceptName);
			if (folder.exists() && folder.isDirectory()) {
				loadDictionaryFolder(folder);
				for (Map.Entry<String,List<String>> entry : randomElements.entrySet()) {
					String key= entry.getKey();
					if (key.equals("RANDOM_EXAMPLE")) {
						List<String> values = entry.getValue();
						selectedRandomElement.put(key, values.get((int) Math.floor(values.size() * Math.random())));
					}
					if (key.equals("HTML_TAGS")) {
						List<String> values = entry.getValue();
						for (String tag : values) {
							htmlTagElements.put(tag.split("\t")[0], tag.split("\t")[1]);	
						}
						
					}
					
					
			
				}
			}
			for (Map.Entry<String,String> entry : selectedRandomElement.entrySet()) {
				this.introText = this.introText.replace(entry.getKey(), entry.getValue());
				this.cancelText = this.cancelText.replace(entry.getKey(), entry.getValue());
				this.acceptText = this.acceptText.replace(entry.getKey(), entry.getValue());
			}
			for (Map.Entry<String,String> entry : htmlTagElements.entrySet()) {
				this.introText = this.introText.replace(entry.getKey(), entry.getValue());
				this.cancelText = this.cancelText.replace(entry.getKey(), entry.getValue());
				this.acceptText = this.acceptText.replace(entry.getKey(), entry.getValue());
			}
		}

		private void loadDictionaryFolder(File dir)
		{
			File[] dictNames = dir.listFiles();

			for (File dictFile : dictNames)
			{
				if (dictFile.isDirectory())
					loadDictionaryFolder(dictFile);
				else if(dictFile.getName().endsWith(".txt"))
				{
					String name = dictFile.getName().replace(".txt", "").toUpperCase();
					randomElements.put(name, loadDictionary(dictFile));
				}
			}
		}
		
		private List<String> loadDictionary(File dict)
		{
			List<String> dictionary = new ArrayList<String>();
			try
			{
				BufferedReader fr = new BufferedReader(new FileReader(dict));

				String line = fr.readLine();
				while (line != null)
				{
					line = line.trim();
					if (line.length() > 0)
					{
						dictionary.add(line.trim());
					}
					line = fr.readLine();
				}
				fr.close();
			}
			catch (Exception e)
			{
				Logger.commonLog(getClass().getSimpleName(), Logger.LOG_ERROR, "Error while reading Dictionary: " + dict.getName() + " (" + e.toString() + ")");
			}
			return dictionary;
		}
	}

	public TutorActor(Agent a)
	{
		super(a);
		introduction_cue_timeout = Integer.parseInt(properties.getProperty("timeout1"));
		introduction_cue_timeout2 = Integer.parseInt(properties.getProperty("timeout2"));
		request_poke_prompt_text = properties.getProperty("requestpokeprompt", request_poke_prompt_text);
		goahead_prompt_text = properties.getProperty("goaheadprompt", goahead_prompt_text);
		response_poke_prompt_text = properties.getProperty("responsepokeprompt",response_poke_prompt_text);
		dont_know_prompt_text = properties.getProperty("dontknowprompt", dont_know_prompt_text);
		moving_on_text = properties.getProperty("moveonprompt", moving_on_text);
		dialogueConfigFile = properties.getProperty("dialogue_config_file",dialogueConfigFile);
		dialogueFolder = properties.getProperty("dialogue_folder",dialogueFolder);
		startAnyways = properties.getProperty("start_anyways","false").equals("true");
		tutorialCondition = properties.getProperty("tutorial_condition",tutorialCondition);
		
		loadDialogConfiguration(dialogueConfigFile);
		
		prioritySource = new BlacklistSource("TUTOR_DIALOG", "");
		((BlacklistSource) prioritySource).addExceptions("TUTOR_DIALOG");
	}

	private void loadDialogConfiguration(String f)
	{
		try
		{
			DOMParser parser = new DOMParser();
			parser.parse(f);
			Document dom = parser.getDocument();
			NodeList dialogsNodes = dom.getElementsByTagName("dialogs");
			if ((dialogsNodes != null) && (dialogsNodes.getLength() != 0))
			{
				Element dialogsNode = (Element) dialogsNodes.item(0);
				NodeList dialogNodes = dialogsNode.getElementsByTagName("dialog");
				if ((dialogNodes != null) && (dialogNodes.getLength() != 0))
				{
					for (int i = 0; i < dialogNodes.getLength(); i++)
					{
						Element dialogElement = (Element) dialogNodes.item(i);
						String conceptName = dialogElement.getAttribute("concept");
						String name = dialogElement.getAttribute("scenario");
						String introText = null;
						String cueText = null;
						String cueAnnotation = null;
						String cancelText = null;
						String cancelAnnotation = null;
						NodeList introNodes = dialogElement.getElementsByTagName("intro");
						if ((introNodes != null) && (introNodes.getLength() != 0))
						{
							Element introElement = (Element) introNodes.item(0);
							introText = introElement.getTextContent();
							/* Behzad, if you want to add hyperlink in dialog-config.xml, you need to do sth here!!!
							 * Right now, you don't know, but you will figure it out. Maybe this place is wrong at all.
							 */
							//introText = introText + " " + "<a href=\"https://www.google.com\">HERE.</a>";
						}
						NodeList cueNodes = dialogElement.getElementsByTagName("accept");
						if ((cueNodes != null) && (cueNodes.getLength() != 0))
						{
							Element cueElement = (Element) cueNodes.item(0);
							cueAnnotation = cueElement.getAttribute("annotation");
							cueText = cueElement.getTextContent();
						}

						NodeList cancelNodes = dialogElement.getElementsByTagName("cancel");
						if ((cancelNodes != null) && (cancelNodes.getLength() != 0))
						{
							Element cancelElement = (Element) cancelNodes.item(0);
							cancelAnnotation = cancelElement.getAttribute("annotation");
							cancelText = cancelElement.getTextContent();
						}
						Dialog d = new Dialog(conceptName, name, introText, cueAnnotation, cueText, cancelAnnotation, cancelText);
						proposedDialogs.put(conceptName, d);
					}
				}
			}
			

		}
		catch (Exception ex)
		{
			ex.printStackTrace();
		}
	}

	protected void processEvent(Event e)
	{
//		if(!System.getProperty("basilica2.agents.condition").contains(tutorialCondition))
//		{
//			return;
//		}
		if(block)
		{
			/*try {
			    Thread.sleep(15000);                 //1000 milliseconds is one second.
			} catch(InterruptedException ex) {
			    Thread.currentThread().interrupt();
			}
			System.out.println("OUT OF SLEEP!");*/
			block = false;
		}
		/* Behzad
		 * Based on the type of event, a function is called to handle it. I need a definition for each Event.
		 */
		if (e instanceof DoTutoringEvent)
		{
			//queue up the start of the tutoring engine.
			
			handleDoTutoringEvent((DoTutoringEvent) e);
			//MessageEvent me = ((DoTutoringEvent) e).getMessageEvent();
			//if(me != null)
			//{
			//	handleRequestDetectedEvent((MessageEvent) me);
			//}
		}
		else if (e instanceof TutoringStartedEvent)
		{
			//start dialog engine
			handleTutoringStartedEvent((TutoringStartedEvent) e);
		}
		else if (e instanceof PresenceEvent)
		{
			//start dialog engine
			PresenceEvent event = (PresenceEvent) e;
			numUser = event.getNumUsers();
		}
		else if (e instanceof PromptEvent)
		{
			PromptEvent event  = (PromptEvent) e;
			if(event.from.equals("INTRODUCTION"))
			{
				block = true;
				System.out.println("GO TO SLEEP!");
			}
		}
		else if (e instanceof MessageEvent)
		{
			//check for concept match and start specific dialog - mostly used for affirmative to 'are you ready'
			handleRequestDetectedEvent((MessageEvent) e);
		}
		else if (e instanceof StudentTurnsEvent)
		{
			//aggregated student input
			handleStudentTurnsEvent((StudentTurnsEvent) e);
		}
		else if (e instanceof MoveOnEvent)
		{
			//someone's decided we should progress the dialog
			handleMoveOnEvent((MoveOnEvent) e);
		}
	}

	private void handleDoTutoringEvent(DoTutoringEvent dte)
	{
		Dialog d = proposedDialogs.get(dte.getConcept());
		if (d != null)
		{
			if(isTutoring)
			{
				if (interruptForNewDialogues)
				{
					//TODONE: respond to start-tutoring command by ending current tutoring session
					sendTutorMessage(moving_on_text);
					DoneTutoringEvent doneEvent = new DoneTutoringEvent(source, currentConcept, true);
					source.queueNewEvent(doneEvent);
					prioritySource.setBlocking(false);
					
	//				TutorTurnsEvent tte = new TutorTurnsEvent(this, new String[] { moving_on_text });
	//				this.dispatchEvent(myAgent.getComponent(tutoring_actor_name), tte);
	//
	//				DoneTutoringEvent dte2 = new DoneTutoringEvent(this, currentConcept, true);
	//				this.broadcast(dte2);
	
					currentAutomata = null;
					currentConcept = null;
					isTutoring = false;
	
					// dialogsReadyQueue.add(d);
					launchDialogOffer(d);
				}
				else
				{
					log(Logger.LOG_WARNING, "Won't start dialogue "+dte.getConcept()+" while current dialog is running - ask again later!");
				}
			}
			else
			{
				launchDialogOffer(d);
			}
		}
	}

	private synchronized void handleRequestDetectedEvent(MessageEvent e)
	{
		/* Behzad
		 * Check here, this function check "accept" and "reject" annotations in dialogues-config
		 * maybe you find a way to choose a dialog by a prompt
		 */
		for(String concept : e.getAllAnnotations())
		{
			Dialog killMeNow = null;

			for(Dialog d : pendingDialogs.values())
			{

				if (d.acceptAnnotation.equals(concept))
				{

					killMeNow = d;
					sendTutorMessage(d.acceptText);
					startDialog(d);
				}
				else if(d.cancelAnnotation.equals(concept))
				{

					killMeNow = d;
					sendTutorMessage(d.cancelText);
					prioritySource.setBlocking(false);
					
				}
				if(killMeNow != null)
				{
					pendingDialogs.remove(killMeNow.acceptAnnotation);
					break;
				}
			}
		}
	}

	public void handleTutoringStartedEvent(TutoringStartedEvent tse)
	{
		
		if(currentConcept.equals(tse.getConcept()))
		{
			List<String> tutorTurns = currentAutomata.start();
			processTutorTurns(tutorTurns);
		}
		else
		{
			log(Logger.LOG_WARNING, "Received start event for "+tse+" but current concept is "+currentConcept);
		}
	}
		
	
	public void startDialog(Dialog d)
	{
		enlistedDialog = null;
		isTutoring = true;
		
		// Launch TuTalkSlim with FuzzyTurnEvaluator
		currentConcept = d.conceptName;
		currentAutomata = new TuTalkAutomata("tutor", "students");
		currentAutomata.setEvaluator(new FuzzyTurnEvaluator());
		currentAutomata.setScenario(Scenario.loadScenario(dialogueFolder  + File.separator + d.scenarioName + ".xml"));
		answerers = new ArrayList<String>();
		//TODONE: figure out what "requests" are and why we care
		TutoringStartedEvent tse = new TutoringStartedEvent(source, d.scenarioName, d.conceptName);
		source.queueNewEvent(tse);
	}

	private void handleMoveOnEvent(MoveOnEvent mve)
	{
		if (expectingResponse)
		{
			if (currentAutomata != null)
			{
				expectingResponse = false;
				noMatchingResponseCount = 0;
				List<Response> expected = currentAutomata.getState().getExpected();
				Response response = expected.get(expected.size() - 1); // Possibly
																		// the
																		// last
																		// one
																		// is
																		// unanticipated-response
				if (!response.getConcept().getLabel().equalsIgnoreCase("unanticipated-response"))
				{
					log(Logger.LOG_ERROR, "Moving on without an Unanticipated-Response Handler. Could be weird!");
				}
				List<String> tutorTurns = currentAutomata.progress(response.getConcept());
				processTutorTurns(tutorTurns);
			}
		}
	}

	private synchronized void handleStudentTurnsEvent(StudentTurnsEvent ste)
	{
		if (expectingResponse)
		{
			if (currentAutomata != null)
			{
				// Evaluate each student turn or evaluate a concatenation!
				if (!ste.getStudentTurns().isEmpty())
				{
					String studentTurn = "";
					for (String turn : ste.getStudentTurns())
					{
						studentTurn += turn + " | ";
					}
					List<EvaluatedConcept> matchingConcepts = currentAutomata.evaluateTuteeTurn(studentTurn, ste.getAnnotations());
					if (matchingConcepts.size() != 0)
					{
						System.out.println(matchingConcepts.get(0).getClass().getSimpleName());
						System.out.println(matchingConcepts.get(0).concept.getClass().getSimpleName());
						Concept concept = matchingConcepts.get(0).concept;
						if (concept.getLabel().equalsIgnoreCase("unanticipated-response"))
						{
							if (!nullExpected)
							{
								// If expecting non-null response and didnt get
								// it, poke for response
								noMatchingResponseCount++;
								if (noMatchingResponseCount <= numUser + 2)
								{
									//TODONE: fire poke event in repsonse to student message
//									TutorTurnsEvent tte = new TutorTurnsEvent(this, new String[] { response_poke_prompt_text,
//											lastTutorTurns.get(lastTutorTurns.size() - 1) });
//									this.dispatchEvent(myAgent.getComponent(tutoring_actor_name), tte);
									//sendTutorMessage(response_poke_prompt_text, lastTutorTurns.get(lastTutorTurns.size() - 1));
									System.out.println("unanticipated");
								}
								else if (noMatchingResponseCount >= numUser + 2)
								{
									// Give up and just go with Unanticipated
									// Response match
									expectingResponse = false;
									noMatchingResponseCount = 0;
									List<String> tutorTurns = currentAutomata.progress(concept);
									processTutorTurns(tutorTurns);
								}
							}
							else
							{
								// If expecting only null response and got it,
								// process it and move on
								expectingResponse = false;
								noMatchingResponseCount = 0;
								List<String> tutorTurns = currentAutomata.progress(concept);
								processTutorTurns(tutorTurns);
							}
						}
						/*else if (concept.getLabel().equalsIgnoreCase("_dont_know_"))
						{

							noMatchingResponseCount++;
//							for (int i = 0; i < ste.getContributors().length; i++)
//							{
//								answerers.add(ste.getContributors()[i]);
//							}
							// Prompt if anyone else wants to try
							//TODONE: respond to "don't know"
//							TutorTurnsEvent tte = new TutorTurnsEvent(this, new String[] { dont_know_prompt_text });
//							this.dispatchEvent(myAgent.getComponent(tutoring_actor_name), tte);
							sendTutorMessage(dont_know_prompt_text);
						}*/
						else
						{
							for (String contributor : ste.getContributors())
							{
								answerers.add(contributor);
							}
							// If Response is non-null, process it
							expectingResponse = false;
							noMatchingResponseCount = 0;
							List<String> tutorTurns = currentAutomata.progress(concept);
							processTutorTurns(tutorTurns);
						}
					}
				}
			}
		}
	}

	private void messageAccepted()
	{
		if (currentAutomata != null)
		{
			List<Response> expected = currentAutomata.getState().getExpected();
			if (expected.size() != 0)
			{
				expectingResponse = true;
				nullExpected = false;
				noMatchingResponseCount = 0;
				//TODONE: respond to 'acknowledge' event -- tutor message has been delivered.
//				this.dispatchEvent(myAgent.getComponent(turn_taker_name), new TutorTurnsEvent(this, new String[0]));

				// Only unanticipated-response expected
				if (expected.size() == 1)
				{
					if (expected.get(0).getConcept().getLabel().equalsIgnoreCase("unanticipated-response"))
					{
						nullExpected = true;
					}
				}
			}
			else
			{
//				TurnCounts tc = TurnCounts.getTurnCounts();
//				if (answerers != null)
//				{
//					for (int i = 0; i < answerers.size(); i++)
//					{
//						tc.addAnswerer(answerers.get(i));
//					}
//				}
//				TurnCounts.commitTurnCounts(tc);
				answerers = null;

				//TODONE: notify all of terminated tutoring session if no more responses are expected.
				DoneTutoringEvent dte = new DoneTutoringEvent(source, currentConcept);
				prioritySource.setBlocking(false);
				source.queueNewEvent(dte);
//				this.broadcast(dte);

				currentAutomata = null;
				currentConcept = null;
				isTutoring = false;
				// if (dialogsReadyQueue.size() != 0) {
				// launchDialog(dialogsReadyQueue.remove(0));
				// }
			}
		}
	}


	private void launchDialogOffer(Dialog d)
	{
		/* Behzad:
		 * In this function, one of greetings sentences will be selected.
		 * The list of greetings are located in /runtime/dialogues/dialogues-config.xml 
		 */
		if (enlistedDialog != null)
		{
			//TODONE: gracefully clear previous dialog if need be (now handling "requests" internally)
//			CancelRequestEvent cre = new CancelRequestEvent(this, enlistedDialog);
//			this.dispatchEvent(myAgent.getComponent(request_detector_name), cre);
			enlistedDialog = null;
		}

		// Prompt IntroText & CueText
		//TODONE: launch intro & cue for dialog
		prioritySource.setBlocking(true);
		sendTutorMessage(d.introText);
//		TutorTurnsEvent tte = new TutorTurnsEvent(this, new String[] {  });
//		this.dispatchEvent(myAgent.getComponent(tutoring_actor_name), tte);

		// Send out Enlist Request Event
		//TODONE: register for concept 'requests'
//		EnlistRequestEvent ere = new EnlistRequestEvent(this, d.cueId, d.conceptName);
//		this.dispatchEvent(myAgent.getComponent(request_detector_name), ere);
		enlistedDialog = d.conceptName;
		//hook up dialog to cue - here, it's any "affirmative" response
		pendingDialogs.put(d.acceptAnnotation, d);

		// Setup timer (or tick count) to poke students if the enlisted request
		// is not responded to yet!
		Timer t = new Timer(introduction_cue_timeout, d.conceptName, this);
		t.start();
	}

	private String selectIntroString(String intro, String userName) {
		// Behzad: randomly select one of the greeting sentences 
		String replacedText = null;
		if(userName != null) {
			replacedText = intro.replaceAll("\\[USERNAME\\]", userName);
		} else {
			replacedText = intro.replaceAll("\\[USERNAME\\]", "");
		}
		
		String[] texts = null;
		texts = replacedText.split(" \\| ");
		return texts[(int)(Math.random()*texts.length)];
	}
	
	private List<String> replaceRandomPhrase(List<String> tutorTurns) {
		// Behzad: Look for the keywords and replace them with random elements or html tags
		for (int i = 0; i < tutorTurns.size(); i++) {
			for (Map.Entry<String,String> entry : this.proposedDialogs.get(this.currentConcept).selectedRandomElement.entrySet()) {
				tutorTurns.set(i, tutorTurns.get(i).replace(entry.getKey(), entry.getValue()));
			}
			for (Map.Entry<String,String> entry : this.proposedDialogs.get(this.currentConcept).htmlTagElements.entrySet()) {
				tutorTurns.set(i, tutorTurns.get(i).replace(entry.getKey(), entry.getValue()));	
			}
		}
		
		
		return tutorTurns;
	}

	private void processTutorTurns(List<String> tutorTurns)
	{
		/* Behzad
		 * Replace RANDOM_ELEMENT with a random phrase which is loacated into data/<conceptName>
		 * 
		 */
		tutorTurns = replaceRandomPhrase(tutorTurns);
		source.userMessages.handleToShortMessages(tutorTurns);

		
		lastTutorTurns = tutorTurns;
		//TODONE: fire pp TutorTurnsEvent too
		String[] turns = tutorTurns.toArray(new String[0]);
		TutorTurnsEvent tte = new TutorTurnsEvent(source, turns);
		
		//gst : should it be here
		if(turns.length == 0)
		{
			return;
		}
		
		source.queueNewEvent(tte);
		//PriorityEvent pete = PriorityEvent.makeBlackoutEvent("TUTOR_DIALOG", new MessageEvent(source, getAgent().getUsername(), join(turns), "TUTOR"), 1.0, 45, 10);
		//((BlacklistSource)pete.getSource()).addExceptions("TUTOR_DIALOG");
		PriorityEvent pete = new PriorityEvent(source, new MessageEvent(source, getAgent().getUsername(), join(turns), "TUTOR"), tutorMessagePriority, prioritySource, tutorTimeout);
		pete.addCallback(new Callback()
		{
			@Override
			public void rejected(PriorityEvent p)
			{
				log(Logger.LOG_ERROR, "Tutor Turn event was rejected. Proceeding anyway...");
				messageAccepted();
			}
			
			@Override
			public void accepted(PriorityEvent p)
			{
				messageAccepted();
			}
		});
		source.pushProposal(pete);
				
		//TODONE: fire message event with expectation of callback.
//		TutorTurnsEvent tte = new TutorTurnsEvent(this, tutorTurns.toArray(new String[0]));
//		tte.setAcknoledgementExpected(true);
//		this.dispatchEvent(myAgent.getComponent(tutoring_actor_name), tte);

		// Waits for AcknowledgeMessage Event and then updates expectations
	}

	public void timedOut(String id)
	{
		Dialog d = null;
		if(proposedDialogs.get(id) == null)
		{
			log(Logger.LOG_WARNING, "No dialog for "+id);
		}
		else
		{
			d = pendingDialogs.get(proposedDialogs.get(id).acceptAnnotation);
		}
		
		log(Logger.LOG_NORMAL, "Timeout for "+id+":"+d);
		if (d != null)
		{
			// If it doesnt match for sometime , poke students once and then
			// forget about it
			String pokePrompt = request_poke_prompt_text;
			//TODONE: Nudge participants if nobody's been responding (correctly, or at all)
//			TutorTurnsEvent tte = new TutorTurnsEvent(this, new String[] { pokePrompt, d.cueText });
//			this.dispatchEvent(myAgent.getComponent(tutoring_actor_name), tte);
			sendTutorMessage(pokePrompt);
			// Start another timer to wait request. If none, then cancel request
			Timer t = new Timer(introduction_cue_timeout2, "CANCEL:" + id, this);
			t.start();
			log(Logger.LOG_NORMAL, "Delaying dialog "+id+" once...");
		}
		else
		{
			if (id.startsWith("CANCEL:"))
			{
				String[] tokens = id.split(":");
				Dialog d2 = proposedDialogs.get(tokens[1]);
				
				d2 = pendingDialogs.remove(d2.acceptAnnotation);
				if (d2 != null)
				{
					//TODONE: continue dialog even if students haven't responded approrpriately.
//					CancelRequestEvent cre = new CancelRequestEvent(this, tokens[1]);
//					this.dispatchEvent(myAgent.getComponent(request_detector_name), cre);
//
//					// Lets just do this dialog and move on!
//					TutorTurnsEvent tte = new TutorTurnsEvent(this, new String[] { goahead_prompt_text });
//					this.dispatchEvent(myAgent.getComponent(tutoring_actor_name), tte);
					
					if(startAnyways)
					{
						sendTutorMessage(goahead_prompt_text);
	
						log(Logger.LOG_NORMAL, "Not delaying "+tokens[1]+" anymore - beginning dialog");
						startDialog(d2);
					}
					else
					{
						sendTutorMessage(d2.cancelText);
						prioritySource.setBlocking(false);
					}
				}
				else
					prioritySource.setBlocking(false);
			}
		}
	}

	private void sendTutorMessage(String... promptStrings)
	{
		String combo = join(promptStrings);

		PriorityEvent pete = new PriorityEvent(source, new MessageEvent(source, getAgent().getUsername(), combo, "TUTOR"), tutorMessagePriority , prioritySource, 45);
		//PriorityEvent pete = PriorityEvent.makeBlackoutEvent("TUTOR_DIALOG", new MessageEvent(source, getAgent().getUsername(), combo, "TUTOR"), 1.0, 45, 10);
		//((BlacklistSource)pete.getSource()).addExceptions("TUTOR_DIALOG");
		source.pushProposal(pete);
		
	}

	public String join(String... promptStrings)
	{
		String combo = "";
		for(String text : promptStrings)
		{
			combo += "|"+text;
		}
		return combo.substring(1);
	}

	public void log(String from, String level, String msg)
	{
		log(level, from + ": " + msg);
	}

	@Override
	public void processEvent(InputCoordinator source, Event event)
	{
		this.source = source;
		processEvent(event);
		
	}

	@Override
	public Class[] getListenerEventClasses()
	{
		return new Class[]{MessageEvent.class, DoTutoringEvent.class,StudentTurnsEvent.class, MoveOnEvent.class, TutoringStartedEvent.class, PresenceEvent.class, PromptEvent.class};
	}

	@Override
	public void preProcessEvent(InputCoordinator source, Event event)
	{
	}

	@Override
	public Class[] getPreprocessorEventClasses()
	{
		return new Class[0];
	}
}
