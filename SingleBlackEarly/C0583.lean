import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0583 : checkSingleBlackFast (19, 5) 6295 .west (-5, 0) (-19, -5) = true := by
  decide +kernel

end LangtonsAnt
