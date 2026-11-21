import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1311 : checkSingleBlackFast (-10, 18) 14148 .north (-1, 5) (1, -27) = true := by
  decide +kernel

end LangtonsAnt
