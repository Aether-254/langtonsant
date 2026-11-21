import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0167 : checkSingleBlackFast (-5, 7) 4660 .north (0, 1) (-14, -9) = true := by
  decide +kernel

end LangtonsAnt
