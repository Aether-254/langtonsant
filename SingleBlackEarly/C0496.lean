import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0496 : checkSingleBlackFast (0, 15) 7307 .west (-5, -2) (-23, -7) = true := by
  decide +kernel

end LangtonsAnt
