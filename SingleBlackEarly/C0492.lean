import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0492 : checkSingleBlackFast (4, 15) 5679 .west (-5, -2) (-19, -3) = true := by
  decide +kernel

end LangtonsAnt
