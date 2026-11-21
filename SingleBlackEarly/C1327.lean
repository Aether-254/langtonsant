import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1327 : checkSingleBlackFast (-14, 18) 13723 .east (-1, -9) (-28, -7) = true := by
  decide +kernel

end LangtonsAnt
