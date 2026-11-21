import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0398 : checkSingleBlackFast (11, -6) 9923 .west (-5, -1) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
