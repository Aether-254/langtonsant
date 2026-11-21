import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0125 : checkSingleBlackFast (4, 8) 7937 .west (-2, -6) (-20, -15) = true := by
  decide +kernel

end LangtonsAnt
