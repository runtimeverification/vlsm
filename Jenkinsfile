pipeline {
  agent {
    dockerfile {
      label 'docker'
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  options { ansiColor('xterm') }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Build and Test') {
      stages {
        stage('Build') { steps { sh '''echo build''' } }
        stage('Test')  { steps { sh '''echo test'''  } }
      }
    }
    stage('Deploy Docs') {
      when { branch 'master' }
      steps {
        sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
          sh '''
            echo "Trigger Doc Update"
          '''
        }
      }
    }
  }
}
