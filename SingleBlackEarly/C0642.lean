import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0642 : checkSingleBlackFast (7, -10) 7467 .west (-11, 0) (-17, -13) = true := by
  decide +kernel

end LangtonsAnt
