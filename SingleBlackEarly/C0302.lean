import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0302 : checkSingleBlackFast (7, 11) 3227 .west (-14, -2) (-13, -16) = true := by
  decide +kernel

end LangtonsAnt
